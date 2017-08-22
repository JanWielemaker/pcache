# Answer caching

## API

:- cache
	p(+atomic, -integer, -list).

Arg has a mode declaration: ++ (ground), + (nonvar), -- (free)

Options:

	- Get variables: V
	- Deduce remaining skeleton
	- Find all solutions
	- Enumerate

p(A, V) :-
	atomic(A),
	(   p_cached(A)
	->  p_cache(A, V)
	;   forall(p_(A,V), assertz(p_cache(A,V)),
	    assertz(p_cached(A))
	).

Or

	trie variant --> list of solutions

...
	trie_lookup(T, Goal, Node),
	(   node_value(Node, '$FALSE')
	->  findall(...)
