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
