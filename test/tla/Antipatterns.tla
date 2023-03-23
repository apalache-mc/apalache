---- MODULE Antipatterns ----
\* Contains a collection of known-to-be-inefficient Apalache constructs

EXTENDS Integers, Apalache, TLC

CONSTANT
  \* @type: Int;
  N


\* Equivalent to S
\* @type: (Set(t)) => Set(t);
RemakeSet(S) ==
  LET 
    \* @type: (Set(t),t) => Set(t);
    addOne(s, e) == s \union {e}
    \* @type: () => Set(t);
    empty == {}
  IN
    ApaFoldSet(addOne, empty, S)

Init == TRUE
Next == TRUE


\* Equivalent to [x \in DOMAIN fn |-> fn[x] + 1]
\* @type: (a -> Int) => a -> Int;
IncrementalFnChange(fn) ==
  LET 
    \* @type: (a -> Int,a) => a -> Int;
    addOneInCdm(f, x) == [f EXCEPT ![x] = f[x] + 1]
  IN
    ApaFoldSet(addOneInCdm, fn, DOMAIN fn)


\* Equivalent to [x \in S |-> A(x)]
\* @type: (Set(a), (a) => b) => a -> b;
IncrementalFnBuild(S, A(_)) ==
  LET 
    \* @type: (a -> b, a) => a -> b;
    extend(f, x) == f @@ (x :> A(x))
    \* @type: () => a -> b;
    emptyFn == [x \in {} |-> A(x)]
  IN
    ApaFoldSet(extend, emptyFn, S)

A(x) == x

Inv == 
  /\ RemakeSet(1..N) = 1..N
  /\ IncrementalFnChange([x \in 1..N |-> x]) = [x \in 1..N |-> x + 1]
  /\ IncrementalFnBuild(1..N, A) = [ x \in 1..N |-> A(x) ]

CInit10 == N = 10
CInit20 == N = 20
CInit40 == N = 40
CInit80 == N = 80
CInit160 == N = 160

====