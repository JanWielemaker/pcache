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
            forget/1,                   % :Goal
            cache_statistics/1          % ?Property
          ]).
:- use_module(library(rocksdb)).
:- use_module(library(error)).
:- use_module(library(lists)).

/** <module> Cached execution of queries

This module allows for transparent caching of query results.
*/

:- meta_predicate
    cached(0),
    forget(0),
    cache_property(0, ?).

:- dynamic
    rocks_d/1.

%!  cache_open(+Directory)
%
%   Open an answer cache in  Directory.   If  Directory  does not exist,
%   create it as an empty answer   store.  Otherwise re-open an existing
%   store.

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

%!  cache_property(:Goal, ?Property) is nondet.
%
%   True if Property is a properly of the cached answers.

cache_property(M:SubGoal, count(Count)) :-
    rocks(DB),
    current_module(M),
    rocks_enum(DB, M:SubGoal, Answers),
    length(Answers, Count).


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
