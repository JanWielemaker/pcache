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
          [ goal_signature/2,
            predicate_callees/2         % :Head, -Callees
          ]).
:- use_module(library(prolog_codewalk)).

:- meta_predicate
    predicate_callees(:, -).


%!  goal_signature(:Goal, -Term)
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

goal_signature(Goal, Term) :-
    Term = Goal.

%!  predicate_hash(:Head, -Hash)
%
%   Compute the hash for a single   predicate. If the predicates clauses
%   can be accessed, this is the variant  hash of all clauses, otherwise
%   it is the variant hash of the head.

predicate_hash(Head, Hash) :-
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

:- thread_local
    calls/1.

predicate_callees(Head, Callees) :-
    findall(CRef, nth_clause(Head, _, CRef), CRefs),
    prolog_walk_code(
        [ clauses(CRefs),
          autoload(true),
          trace_reference(_:_),
          on_trace(track_ref),
          source(false)
        ]),
    findall(Callee, retract(calls(Callee)), Callees).

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
