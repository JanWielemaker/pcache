/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2017, VU University Amsterdam
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(cache_rocks,
          [ cache_open/1,               % +Directory
            cached/1,                   % :Goal
            cached/2,                   % :Goal, +Hash
            cache_property/2,           % :Goal, ?Property
            cache_properties/2,         % :Goal, ?Properties:dict
            forget/1,                   % :Goal
            cache_statistics/1,         % ?Property
            cache_listing/0,
            cache_listing/1             % +Options
          ]).
:- use_module(library(rocksdb)).
:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(debug)).
:- use_module(library(option)).
:- use_module(signature).

/** <module> Persistent answer caching

This module implements persistent caching   of  answers. The inspiration
comes from tabled execution where tabled answers   are kept as a trie of
tries. The outer trie maps goal variants  to answer tries and the answer
tries  provide  the  answers   to   a    specific   goal   variant.  The
library(rocksdb) (and library(bdb)) provide a persistent Key-Value store
that can map a term to a term.   The term is represented as an _external
record_, basically a  binary  alternative   to  write/read.  This binary
representation is a _blob_ for the   key-value store. The representation
represents a variant, currently with two limitations:

  1. If the term has internal sharing, it is different from a term
     without.  E.g., `A = f(X), B = b(A,A)` is a different `B` than
     you get from `B = b(f(X),f(X))`.
  2. If the key is cyclic, it only matches internally equivalent
     cycles.  E.g., `A = [a|A]` and `A = [a,a|A]` are considered
     different.

Ignoring these two issues (which can be   fixed),  we can use RocksDB or
BDB as the _outer_ trie used in tabling.  We could use a trie or similar
structure for the set of answers, but in  this case a list preserves the
original order and is more  compact.   Our  database basically maps call
variants to a list of answers.

In  addition,  it  does  some  book  keeping.  First  of  all,  it  uses
signature.pl to compute a _deep hash_ of   the predicate. A deep hash is
an SHA1 hash computed  from  the  clauses   of  the  predicates  and all
predicates called by  it.  The  original   goal,  say  m:p(a1,  ...)  is
translated into <SHA1>(a1, ...). This implies  that changing a predicate
or one of the predicates called by   it invalidate the cache. Second, it
keeps track of partially completed  goals   and  fully  completed goals.
Re-running a fully completed goal simply   retrieves the cached answers.
Re-running a partially completed goal first retrieves the cached answers
and then re-runs the goal with an  offset to compute additional answers,
updating the status.
*/

:- meta_predicate
    cached(0),
    cached(:, +),
    forget(:),
    cache_property(:, ?),
    offset_check(+, 0, +).

:- dynamic
    rocks_d/2.

%!  cache_open(+Directory)
%
%   Open an answer cache in  Directory.   If  Directory  does not exist,
%   create it as an empty answer   store.  Otherwise re-open an existing
%   store.

cache_open(Dir) :-
    rocks_d(_, Dir),
    !.
cache_open(Dir) :-
    rocks_d(_, _),
    permission_error(open, cache, Dir).
cache_open(Dir) :-
    rocks_open(Dir, DB,
               [ key(term),
                 value(term)
               ]),
    asserta(rocks_d(DB, Dir)).

rocks(DB) :-
    rocks_d(DB, _),
    !.
rocks(_) :-
    existence_error(cache, answers).

%!  cached(:Goal)
%
%   This predicate is logically equivalent to Goal. However, answers are
%   on the first call collected in a   trie and subsequently returned in
%   arbitrary (hash key) order without duplicates.

cached(G) :-
    rocks(DB),
    goal_signature(G, Signature, Vars),
    (   rocks_get(DB, Signature, cache(G, Answers, State, _Time, _Hash))
    ->  from_db(State, Vars, Answers, restart(G, Signature, DB))
    ;   generalise_goal(G, 2, General, Bindings),
        goal_signature(General, GenSignature, GenVars),
        rocks_get(DB, GenSignature,
                  cache(GenGoal, GenAnswers, State, Time, Hash))
    ->  debug(cache, 'Filtering ~p for ~p', [GenGoal, G]),
        maplist(bind, Bindings),
        findall(Vars, member(GenVars, GenAnswers), Answers),
        rocks_put(DB, Signature, cache(G, Answers, State, Time, Hash)),
        member(Vars, Answers)
    ;   cache(G, Signature, Vars, [], DB)
    ).

bind(V=V).

cache(G, Sign, Vars, Sofar, DB) :-
    get_time(Now),
    copy_term(G+Sign, Goal+Signature),
    functor(Signature, Hash, _),
    Cache = cache(Goal, _Answers, _State, Now, Hash),
    (   Sofar == []
    ->  Enum = (G, add_answer(Set, Vars))
    ;   Enum = (offset_check(Vars, G, Sofar), add_answer(Set, Vars))
    ),
    setup_call_catcher_cleanup(
        answer_set(Sofar, Set),
        Enum,
        Catcher,
        commit(Catcher, Set, Signature, Cache, DB)).

commit(exit, Set, Signature, Cache, DB) :-
    answers(Set, Answers),
    set_cache(Cache, Answers, complete),
    rocks_put(DB, Signature, Cache).
commit(fail, Set, Signature, Cache, DB) :-
    answers(Set, Answers),
    set_cache(Cache, Answers, complete),
    rocks_put(DB, Signature, Cache).
commit(!, Set, Signature, Cache, DB) :-
    answers(Set, Answers),
    set_cache(Cache, Answers, partial),
    rocks_put(DB, Signature, Cache).
commit(exception(E), Set, Signature, Cache, DB) :-
    answers(Set, Answers),
    set_cache(Cache, Answers, exception(E)),
    rocks_put(DB, Signature, Cache).
commit(external_exception(_), Set, Signature, Cache, DB) :-
    answers(Set, Answers),
    set_cache(Cache, Answers, partial),
    rocks_put(DB, Signature, Cache).

from_db(complete, Vars, Answers, _Restart) :-
    member(Vars, Answers).
from_db(partial, Vars, Answers, restart(G, Signature, DB)) :-
    (   member(Vars, Answers)
    ;   cache(G, Signature, Vars, Answers, DB)
    ).
from_db(exception(E), Vars, Answers, _Restart) :-
    (   member(Vars, Answers)
    ;   throw(E)
    ).


set_cache(cache(_Goal, Answers, State, _Now, _Hash), Answers, State).

%!  answer_set(+List0, -Answers) is det.
%!  add_answer(+Answers, +Answer) is det.
%!  answers(+Answers, -List) is det.

answer_set([], answers(List, List)) :-
    !,
    List = [$|_].
answer_set(Set0, answers([$|OpenSet], Tail)) :-
    open_list(Set0, OpenSet, Tail2),
    Tail = Tail2.                       % delay unification to avoid
                                        % Tail becoming a reference chain
open_list([Last], T, T) :-
    !,
    T = [Last|_].
open_list([H|T0], [H|T], Last) :-
    open_list(T0, T, Last).

add_answer(Set, A) :-
    arg(2, Set, T0),
    duplicate_term(A, A2),
    nb_linkarg(2, T0, [A2|_]),
    arg(2, T0, T),
    nb_linkarg(2, Set, T).

answers(answers([$|Answers], T), Answers) :-
    arg(2, T, []).

%!  offset_check(+Template, :Goal, +Expected)
%
%   Skip the first Expected answers from Goal.   Raise an exception if a
%   produced answer is not a variant of Template.

offset_check(Template, Goal, Expected) :-
    State = state(Expected),
    Goal,
    arg(1, State, Answers),
    (   Answers == []
    ->  true
    ;   Answers = [First|More],
        (   First =@= Template
        ->  nb_linkarg(1, State, More),
            fail
        ;   throw(error(consistency_error(Goal, Template, First),_))
        )
    ).

%!  generalise_goal(:Goal, +MaxDepth, -General, -Bindings) is nondet.
%
%   True  when  General  is  a  generalization    of  Goal  achieved  by
%   generalising terms in Bindings. Bindings  is   a  list of `Term=Var`
%   pairs.  Generalization  first  turns  a  compound  entirely  into  a
%   variable  before  preserving  the  functor    and  generalizing  the
%   arguments.
%
%   @arg MaxDepth defines how deep we   look into arguments for possible
%   generalizations. When `1`, we  merely   replace  nonvar arguments of
%   Goal with a variable.

generalise_goal(M:G0, MaxDepth, M:G, Bindings) :-
    generalise(MaxDepth, G0, G, [], Bindings),
    nonvar(G),
    G0 \== G.

generalise(_, Term, Term, Bindings, Bindings).
generalise(_, Term, Var, Bindings0, Bindings) :-
    nonvar(Term),
    Bindings = [Term=Var|Bindings0].
generalise(MaxDepth, Term, Gen, Bindings0, Bindings) :-
    succ(MaxDepth2, MaxDepth),
    compound(Term),
    compound_name_arguments(Term, Name, Args0),
    foldl(generalise(MaxDepth2), Args0, Args, Bindings0, Bindings),
    compound_name_arguments(Gen, Name, Args),
    Gen \== Term.

%!  cached(:Goal, +Hash)
%
%   Get the answers for Goal from an   old hashed result. Hash is either
%   the full hash or a _shorthash_ (7 character prefix).

cached(Goal, HashS) :-
    atom_string(Hash, HashS),
    is_hash(Hash, Type),
    rocks(DB),
    cached(Type, DB, Goal, Hash).

cached(sha1, DB, M:Goal, Hash) :-
    (   Goal =.. [_|Args],
        Signature =.. [Hash|Args],
        rocks_get(DB, Signature,
                  cache(M:Goal, Answers, _State, _Time, _Hash))
    ->  term_variables(Goal, VarList),
        Vars =.. [v|VarList],
        member(Vars, Answers)
    ;   generalise_goal(M:Goal, 5, M:General, Bindings),
        General =.. [_|Args],
        Signature =.. [Hash|Args],
        rocks_get(DB, Signature,
                  cache(M:GenGoal, GenAnswers, _State, _Time, _Hash))
    ->  debug(cache, 'Filtering ~p for ~p', [GenGoal, Goal]),
        term_variables(General, VarList),
        GenVars =.. [v|VarList],
        maplist(bind, Bindings),
        member(GenVars, GenAnswers)
    ;   existence_error(answer_cache, Hash)
    ).
cached(short, DB, Goal, ShortHash) :-
    Cache = cache(GoalV, Answers, _State, _Now, Hash),
    rocks_enum(DB, _Key, Cache),
    sub_atom(Hash, 0, _, _, ShortHash),
    !,
    (   Goal =@= GoalV
    ->  term_variables(Goal, VarList),
        Vars =.. [v|VarList],
        member(Vars, Answers)
    ;   subsumes_term(GoalV, Goal)
    ->  term_variables(GoalV, VarList),
        GenVars =.. [v|VarList],
        Goal = GoalV,
        member(GenVars, Answers)
    ;   throw(error(specific_expected(Goal, GoalV, ShortHash), _))
    ).

is_hash(Atom, Hash) :-
    atom_length(Atom, Len),
    (   Len == 40
    ->  Hash = sha1
    ;   Len == 7
    ->  Hash = short
    ;   domain_error(hash, Atom)
    ).

%!  cache_property(:Goal, ?Property) is nondet.
%!  cache_properties(:Goal, ?Properties:dict) is nondet.
%
%   True if Property is a  properly  of   the  cached  answers for Goal.
%   Defined properties are:
%
%     - count(-Count)
%     Number of answers
%     - hash(-Hash)
%     Deep hash of the predicate associated with the goal.
%     - time_cached(-Time)
%     Time stamp when the cache was created.
%
%   The cache_properties/2 variant returns all properties  of a cache in
%   a dict using the above keys.

cache_property(M:SubGoal, Property) :-
    rocks(DB),
    Cache = cache(M:SubGoal, _Answers, _Time, _Hash),
    rocks_enum(DB, _, Cache),
    property(Property, Cache).

property(count(Count), cache(_, Answers, _, _)) :-
    length(Answers, Count).
property(time_cached(Time), cache(_, _, Time, _)).
property(hash(Hash), cache(_, _, _, Hash)).

cache_properties(M:SubGoal,
                 cache_properties{count:Count,
                                  time_cached:Time,
                                  state:State,
                                  hash:Hash
                                 }) :-
    rocks(DB),
    Cache = cache(M:SubGoal, Answers, State, Time, Hash),
    rocks_enum(DB, _, Cache),
    length(Answers, Count).

%!  forget(:Goal)
%
%   Forget all cached results that are  subsumed by Goal. Typically used
%   as forget(m:p(_,_)) to remove all  data   cached  for m:p/2. Notably
%   forget(_:_) will destroy the entire cache.

forget(Goal) :-
    rocks(DB),
    Cache = cache(CGoal, _Answers, _State, _Now, _Hash),
    forall(( rocks_enum(DB, Key, Cache),
             subsumes_term(Goal, CGoal)
           ),
           rocks_delete(DB, Key)).

%!  cache_statistics(?Key)
%
%   True when Key is a know statistics about the caching mechanism.

cache_statistics(Property) :-
    rocks(DB),
    rocks_property(DB, Property).

%!  cache_listing is det.
%!  cache_listing(+Options) is det.
%
%   List contents of the persistent cache.

cache_listing :-
    cache_listing([]).

cache_listing(Options) :-
    format('Predicate ~t Cached at~55|    Hash State ~t Count~76|~n', []),
    format('~`=t~76|~n'),
    forall(setof(Variant-Properties,
                 cached_predicate(Pred, Variant, Properties), PList),
           report(Pred, PList, Options)).

cached_predicate(M:Name/Arity, Goal, Properties) :-
    cache_properties(M:Goal, Properties),
    functor(Goal, Name, Arity).


report(M:Name/Arity, Variants, Options) :-
    length(Variants, VCount),
    format('~w:~w/~d (~D variants)~n', [M, Name, Arity, VCount]),
    forall(limit(10, member(Variant-Properties, Variants)),
           ( short_state(Properties.state, State),
             short_hash(Properties.hash, M:Variant, Hash, Options),
             format_time(string(Date), "%FT%T", Properties.time_cached),
             numbervars(Variants, 0, _, [singletons(true)]),
             format('  ~p ~`.t ~s~55| ~w ~`.t ~w ~69| ~`.t ~D~76|~n',
                    [Variant, Date, Hash, State, Properties.count])
           )),
    Skipped is VCount - 10,
    (   Skipped > 0
    ->  format('  (skipped ~D variants)~n', [Skipped])
    ;   true
    ).

short_state(complete,     'C').
short_state(partial,      'P').
short_state(exception(_), 'E').

short_hash(Hash, Variant, Short, Options) :-
    option(hash(long), Options),
    !,
    (   deep_predicate_hash(Variant, Hash)
    ->  string_concat(Hash, *, Short)
    ;   Short = Hash
    ).
short_hash(Hash, Variant, Short, _) :-
    sub_string(Hash, 0, 7, _, Short0),
    (   deep_predicate_hash(Variant, Hash)
    ->  string_concat(Short0, *, Short)
    ;   Short = Short0
    ).

:- multifile prolog:error_message//1.

prolog:error_message(consistency_error(Goal, Template, First)) -->
    [ '~p yielded inconsistent results (~p \\=@= ~p)'-[Goal, Template, First] ].
prolog:error_message(specific_expected(Goal, Expected, _Hash)) -->
    [ '~p is not a specialization of ~p'-[Goal, Expected] ].

:- multifile sandbox:safe_meta_predicate/1.

sandbox:safe_meta_predicate(cache_rocks:cached/1).
sandbox:safe_meta_predicate(cache_rocks:forget/1).
