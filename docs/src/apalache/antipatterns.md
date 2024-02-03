# Antipatterns

This page collects known antipaterns (APs) when writing TLA+ for Apalache. In this context, APs are syntactic forms or specification approaches that, for one reason or another, have particularly slow/complex encodings for the target model checker. For a pattern to be an AP, there must exist a known, equivalent, efficient pattern. 

Often, APs arise from a user's past experiences with writing TLA+ for TLC, or from a direct translation of imperative OOP code into TLA+, as those follow a different paradigm, and therefore entail different cost evaluation of which expressions are slow/complex and which are not.

## `CHOOSE`-based recursion

Often, operators that represent operations over sets have the following shape:
```tla
RECURSIVE F(_)
F(S) == 
  IF S == {}
  THEN v
  ELSE 
    LET e == CHOOSE x \in S: TRUE
    IN G(F( S \ {e} ), e )
```

For example, one can implement `min/max` operators this way:
```tla
RECURSIVE min(_)
min(S) == 
  IF S == {}
  THEN Infinity
  ELSE 
    LET e == CHOOSE x \in S: TRUE
    IN LET minOther == min( S \ {e} )
    IN IF e < minOther THEN e ELSE minOther 
```

Apalache dislikes the use of the above, for several reasons. Firstly, since the operator is `RECURSIVE`, Apalache does not support it after version 0.23.1. In earlier versions Apalache requires a predefined upper bound on unrolling, which means that the user must know, ahead of time, what the largest `|S|` is, for any set `S`, to which this operator is ever applied. 
In addition, computing `F` for a set `S` of size `n = |S|` requires `n` encodings of a `CHOOSE` operation, which can be considerably expensive in Apalache.
Lastly, Apalache also needs to encode all of the the `n` intermediate sets, `S \ {e1}`, `(S \ {e1}) \ {e2}`, `((S \ {e1}) \ {e2}) \ {e3}`, and so on.

The AP above can be replaced by a very simple pattern:
```tla
F(S) == ApaFoldSet( G, v, S )
```

`ApaFoldSet` (and `ApaFoldSeqLeft`) were introduced precisely for these scenarios, and should be used over `RECURSIVE + CHOOSE` in most cases.

## Incremental computation
Often, users introduce an expression `Y`, which is derived from another expression `X` (`Y == F(X)`, for some `F`). Instead of defining `Y` directly, in terms of the properties it possesses,  it is possible to define all the intermediate steps of transforming `X` into `Y`: "`X` is slightly changed into `X1` (e.g. by adding one element to a set, or via `EXCEPT`), which is changed into `X2`, etc. until `Xn = Y`". Doing this in Apalache is almost always a bad idea, if a direct characterization of `Y` exists.

Concretely, the following constructs are APs:
1. Incremental `EXCEPT`
```tla
G ==
  LET F(g, x) == [g EXCEPT ![x] = A(x)]
  IN ApaFoldSet(F, f, S)
```

2. Incremental `\union`
```tla
R ==
  LET F(T, e) == T \union {A(e)}
  IN ApaFoldSet(F, S0, S)
```

3. Chained `@@/:>`
```tla
f == ( k1 :> A(k1) ) @@ ( k2 :> A(k2) ) @@ ... @@ ( kn :> A(kn) ) 
```

For example:
```tla
f == [ x \in 1..20 |-> 0 ]
Y == 
  LET F(g, x) == [g EXCEPT ![x] = x * x]
  IN ApaFoldSet(F, f, 7..12 )
```

TLC likes these sorts of operations, because it manipulates programming-language objects in its own implementation.
This makes it easy to construct temporary mutable objects, manipulate them (e.g. via for-loops) and garbage-collect them after they stop being useful.
For constraint-based approaches, like Apalache, the story is different.
Not only are these intermediate steps not directly useful (since Apalache is not modeling TLA+ expressions as objects in Scala),
they actually hurt performance, since they can generate a significant amount of constraints,
which are all about describing data structures (e.g. two functions being almost equal, except at one point).
Essentially, Apalache is spending its resources not on state-space exploration, but on in-state value computation, which is not its strong suit.
Below we show how to rewrite these APs.

1. Incremental `EXCEPT`: Replace
```tla
G ==
  LET F(g, x) == [g EXCEPT ![x] = A(x)]
  IN ApaFoldSet(F, f, S)
```
with
```tla
G == 
[ x \in DOMAIN f |->
  IF x \in S
  THEN A(x)
  ELSE f[x]
]
```

2. Incremental `\union`: Replace
  ```tla
  R ==
    LET F(T, e) == T \union {A(e)}
    IN ApaFoldSet(F, S0, S)
  ```
with
```tla
R == S0 \union { A(e): e \in S }
```

3. Iterated `@@/:>`: Replace
```tla
f == ( k1 :> A(k1) ) @@ ( k2 :> A(k2) ) @@ ... @@ ( kn :> A(kn) ) 
```
with
```tla
f == [ k \in {k1,...,kn} |-> A(k) ]
```

