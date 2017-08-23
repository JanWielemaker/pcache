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

:- module(trie_cache,
          [ cached/1,                           % :Goal
            forget/1,                           % :Goal
            cache_statistics/1
          ]).
:- use_module(library(aggregate)).

/** <module> Cached execution of queries

This module allows for transparent caching of query results.
*/

:- meta_predicate
    cached(0),
    forget(0).

:- dynamic
    trie_d/1.

trie(T) :-
    trie_d(T),
    !.
trie(T) :-
    trie_new(T),
    asserta(trie_d(T)).

%!  cached(:Goal)
%
%   This predicate is logically equivalent to Goal. However, answers are
%   on the first call collected in a   trie and subsequently returned in
%   arbitrary (hash key) order without duplicates.

cached(G) :-
    trie(T),
    (   trie_lookup(T, G, Answers)
    ->  trie_gen(Answers, G, _)
    ;   trie_new(Answers),
        (   G,
            trie_insert(Answers, G, true),
            fail
        ;   (   trie_insert(T, G, Answers)
            ->  trie_gen(Answers, G, _)
            ;   trie_destroy(Answers),
                trie_lookup(T, G, OldAnswers),
                trie_gen(OldAnswers, G, _)
            )
        )
    ).

%!  forget(:Goal)
%
%   Forget all cached results that unify with Goal.

forget(M:SubGoal) :-
    trie(VariantTrie),
    current_module(M),
    forall(trie_gen(VariantTrie, M:SubGoal, Trie),
           (  trie_delete(VariantTrie, M:SubGoal, _),
              trie_destroy(Trie)
           )).


%!  cache_statistics(?Key)
%
%   True when Key is a know statistics about the caching mechanism.

cache_statistics(memory(Total)) :-
    aggregate_all(sum(Bytes), trie_property(_, size(Bytes)), Total).
