:- module(cache_rocks,
          [ cache_open/1,			% +Directory
            cached/1,                           % :Goal
            forget/1,                           % :Goal
            cache_statistics/1
          ]).
:- use_module(library(rocksdb)).
:- use_module(library(error)).
:- use_module(library(lists)).

/** <module> Cached execution of queries

This module allows for transparent caching of query results.
*/

:- meta_predicate
    cached(0),
    forget(0).

:- dynamic
    rocks_d/1.

cache_open(Dir) :-
    rocks_d(_),
    permission_error(open, cache, Dir).
cache_open(Dir) :-
    rocks_open(Dir, DB,
               [ key(term),
                 value(term)
               ]),
    asserta(rocks_d(DB)).

rocks(DB) :-
    rocks_d(DB),
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
    (   rocks_get(DB, G, Answers)
    ->  member(G, Answers)
    ;   findall(G, G, Answers),
        rocks_put(DB, G, Answers),
        member(G, Answers)
    ).

%!  forget(:Goal)
%
%   Forget all cached results that unify with Goal.

forget(M:SubGoal) :-
    rocks(DB),
    current_module(M),
    forall(rocks_enum(DB, M:SubGoal, _Answers),
           (  rocks_delete(DB, M:SubGoal)
           )).

%!  cache_statistics(?Key)
%
%   True when Key is a know statistics about the caching mechanism.

cache_statistics(Property) :-
    rocks(DB),
    rocks_property(DB, Property).
