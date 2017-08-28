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
            cache_property/2,           % :Goal, ?Property
            cache_properties/2,         % :Goal, ?Properties:dict
            forget/1,                   % :Goal
            cache_statistics/1,         % ?Property
            cache_listing/0
          ]).
:- use_module(library(rocksdb)).
:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(signature).

/** <module> Cached execution of queries

This module allows for transparent caching of query results.
*/

:- meta_predicate
    cached(0),
    forget(0),
    cache_property(0, ?),
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
    ;   cache(G, Signature, Vars, [], DB)
    ).

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
    current_module(M),
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
    current_module(M),
    Cache = cache(M:SubGoal, Answers, State, Time, Hash),
    rocks_enum(DB, _, Cache),
    length(Answers, Count).

%!  forget(:Goal)
%
%   Forget all cached results that unify with Goal.

forget(M:SubGoal) :-
    rocks(DB),
    forall((  current_module(M),
              rocks_enum(DB, M:SubGoal, _Answers)
           ),
           rocks_delete(DB, M:SubGoal)).

%!  cache_statistics(?Key)
%
%   True when Key is a know statistics about the caching mechanism.

cache_statistics(Property) :-
    rocks(DB),
    rocks_property(DB, Property).

%!  cache_listing
%
%   List contents of the persistent cache.

cache_listing :-
    format('Predicate ~t Cached at~62| State ~t Count~76|~n', []),
    format('~`=t~76|~n'),
    forall(setof(Variant-Properties,
                 cached_predicate(Pred, Variant, Properties), PList),
           report(Pred, PList)).

cached_predicate(M:Name/Arity, Goal, Properties) :-
    cache_properties(M:Goal, Properties),
    functor(Goal, Name, Arity).


report(M:Name/Arity, Variants) :-
    length(Variants, VCount),
    format('~w:~w/~d (~D variants)~n', [M, Name, Arity, VCount]),
    forall(limit(10, member(Variant-Properties, Variants)),
           ( short_state(Properties.state, State),
             format_time(string(Date), "%+", Properties.time_cached),
             numbervars(Variants, 0, _, [singletons(true)]),
             format('  ~p ~`.t ~s~62| ~`.t ~w ~69| ~`.t ~D~76|~n',
                    [Variant, Date, State, Properties.count])
           )),
    Skipped is VCount - 10,
    (   Skipped > 0
    ->  format('  (skipped ~D variants)~n', [Skipped])
    ;   true
    ).

short_state(complete, 'C').
short_state(partial, 'P').
short_state(exception(_), 'E').
