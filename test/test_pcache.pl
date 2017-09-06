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

:- module(test_pcache,
          [ test_pcache/0
          ]).
:- use_module(user:'../prolog/cache_rocks').
:- use_module('../prolog/cache_rocks').
:- use_module(library(plunit)).
:- use_module(library(filesex)).
:- use_module(library(debug)).

test_pcache :-
    run_tests([ pcache
              ]).

:- begin_tests(pcache,
               [ setup(create_test_db(Dir)),
                 cleanup(clean_db(Dir))
               ]).

test(open, Xs == [8]) :-
    add_table(2),
    findall(X, cached(table(2, 4, X)), Xs),
    assertion((cache_property(table(2, 4, _), count(Count)), Count =:= 1)).

:- end_tests(pcache).

		 /*******************************
		 *              DATA		*
		 *******************************/

:- dynamic table/3.

add_table(N) :-
    forall(between(1, 10, I),
           (   V is N*I,
               assertz(table(N, I, V))
           )).

clean_db :-
    retractall(table(_,_,_)).


		 /*******************************
		 *         DB MANAGEMENT	*
		 *******************************/

create_test_db(Dir) :-
    current_prolog_flag(pid, P),
    atom_concat('test-db-', P, Dir),
    cache_open(Dir).

clean_db(Dir) :-
    cache_close,
    delete_directory_and_contents(Dir),
    clean_db.
