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

:- module(signature,
          [ goal_signature/2,           % :Goal, -Signature
            goal_signature/3,           % :Goal, -Signature, -Vars
            deep_predicate_hash/2,      % :Head, -Hash
            predicate_callees/2,        % :Head, -Callees
            predicate_dependencies/2    % :Head, -Dependencies
          ]).
:- use_module(library(prolog_codewalk)).
:- use_module(library(ordsets)).
:- use_module(library(apply)).

:- meta_predicate
    goal_signature(:, -),
    goal_signature(:, -, -),
    predicate_callees(:, -),
    deep_predicate_hash(:, -),
    predicate_dependencies(:, -).


%!  goal_signature(:Goal, -Term) is det.
%!  goal_signature(:Goal, -Term, -Vars) is det.
%
%   Replace the module and functor of  Goal   with  a hash. For example,
%
%       user:between(1, 5, X),
%
%   becomes something like this:
%
%       '931be36e3ed89e766d332277a61664ff3c08d56a'(1, 5, X).
%
%   The hash is based on the   predicate and predicates reachable though
%   the call graph for the most generic form.
%
%   @arg Vars is a term holding the variables in Goal/Term (these are
%   the same).

goal_signature(M:Goal, Term) :-
    deep_predicate_hash(M:Goal, Hash),
    Goal =.. [_|Args],
    Term =.. [Hash|Args].

goal_signature(Goal, Term, Vars) :-
    goal_signature(Goal, Term),
    term_variables(Term, VarList),
    Vars =.. [v|VarList].

%!  deep_predicate_hash(:Head, -Hash) is det.
%
%   Compute the predicate hash of Head and   all its callees and combine
%   this into a single hash.

deep_predicate_hash(Head, Hash) :-
    predicate_dependencies(Head, Callees),
    maplist(predicate_hash, Callees, Hashes),
    variant_sha1(Hashes, Hash).

%!  predicate_hash(:Head, -Hash)
%
%   Compute the hash for a single   predicate. If the predicates clauses
%   can be accessed, this is the variant  hash of all clauses, otherwise
%   it is the variant hash of the head.

:- dynamic predicate_hash_c/4.

predicate_hash(M:Head, Hash) :-
    predicate_hash_c(Head, M, Gen, Hash0),
    predicate_generation(M:Head, Gen),
    !,
    Hash = Hash0.
predicate_hash(M:Head, Hash) :-
    retractall(predicate_hash_c(Head, M, _, _)),
    predicate_hash_nc(M:Head, Hash0),
    predicate_generation(M:Head, Gen),
    assertz(predicate_hash_c(Head, M, Gen, Hash0)),
    Hash = Hash0.

predicate_hash_nc(Head, Hash) :-
    implementation(Head, Head1),
    (   predicate_property(Head1, interpreted)
    ->  findall((Head1:-Body), clause(Head1,Body), Clauses),
        variant_sha1(Clauses, Hash)
    ;   variant_sha1(Head1, Hash)
    ).

implementation(M0:Head, M:Head) :-
    predicate_property(M0:Head, imported_from(M1)),
    !,
    M = M1.
implementation(Head, Head).

%!  predicate_dependencies(:Head, -Callees:list(callable)) is det.
%
%   True when Callees is a set (ordered list) of all predicates that are
%   directly or indirectly reachable through Head.
%
%   @tbd: speedup finding whether some dependency changed.  Some ideas
%
%     - Organise dependencies by module and keep track of a
%     last_modified_generation per module, so we can tick of entire
%     modules.
%     - Have a DB notification service and pro-actively invalidate
%     dependencies.

:- dynamic predicate_dependencies_c/3.

predicate_dependencies(M:Head, Callees) :-
    predicate_dependencies_c(Head, M, Callees0),
    maplist(not_modified, Callees0),
    !,
    Callees = Callees0.
predicate_dependencies(M:Head, Callees) :-
    retractall(predicate_dependencies_c(Head, M, _)),
    predicate_dependencies_nc(M:Head, Callees0),
    assertz(predicate_dependencies_c(Head, M, Callees0)),
    Callees = Callees0.

not_modified(M:Head) :-
    predicate_callees_c(Head, M, Gen, _Callees0),
    predicate_generation(M:Head, Gen).

predicate_dependencies_nc(Head, Callees) :-
    ground(Head, GHead),
    predicate_dependencies(Head, [GHead], Callees0),
    maplist(generalise, Callees0, Callees).

predicate_dependencies(Head, Callees0, Callees) :-
    predicate_callees(Head, Called),
    maplist(ground, Called, GCalled),
    ord_subtract(GCalled, Callees0, New),
    (   New == []
    ->  Callees = Callees0
    ;   ord_union(Callees0, GCalled, Callees1),
        foldl(predicate_dependencies, New, Callees1, Callees)
    ).

ground(Term, Ground) :-
    generalise(Term, Term2),
    copy_term(Term2, Ground),
    numbervars(Ground, 0, _).

:- thread_local
    calls/1.

:- dynamic predicate_callees_c/4.

predicate_callees(M:Head, Callees) :-
    predicate_callees_c(Head, M, Gen, Callees0),
    predicate_generation(M:Head, Gen),
    !,
    Callees = Callees0.
predicate_callees(M:Head, Callees) :-
    retractall(predicate_callees_c(Head, M, _, _)),
    predicate_callees_nc(M:Head, Callees0),
    predicate_generation(M:Head, Gen),
    assertz(predicate_callees_c(Head, M, Gen, Callees0)),
    Callees = Callees0.

predicate_callees_nc(Head0, Callees) :-
    generalise(Head0, Head),
    findall(CRef, nth_clause(Head, _, CRef), CRefs),
    prolog_walk_code(
        [ clauses(CRefs),
          autoload(true),
          trace_reference(_:_),
          on_trace(track_ref),
          source(false)
        ]),
    findall(Callee, retract(calls(Callee)), Callees0),
    sort(Callees0, Callees).

:- public track_ref/3.

track_ref(Callee0, _Caller, _Location) :-
    generalise(Callee0, Callee1),
    implementation(Callee1, Callee),
    (   calls(Callee)
    ->  true
    ;   assertz(calls(Callee))
    ).

generalise(M:Head0, M:Head) :-
    functor(Head0, Name, Arity),
    functor(Head, Name, Arity).

predicate_generation(Head, Gen) :-
    predicate_property(Head, last_modified_generation(Gen0)),
    !,
    Gen = Gen0.
predicate_generation(_, 0).
