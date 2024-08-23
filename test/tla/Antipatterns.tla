---- MODULE Antipatterns ----
(* Contains a collection of known-to-be-inefficient Apalache constructs, a.k.a. "antipatterns".
We explain why these constructs are inefficient in 
https://apalache-mc.org/docs/apalache/antipatterns.html

The purpose of this file is to collect known antipatterns, so we can measure just how 
much they affect performance, across various versions of Apalache.
As a side-effect of the work done on ADR20, the performance hit when using anipatterns,
while still present, is expected to be less drastic than before.
*)

EXTENDS Integers, Apalache, TLC, Sequences

CONSTANT
  \* @type: Int;
  N

CInit10 == N = 10
CInit20 == N = 20
CInit40 == N = 40
CInit80 == N = 80
CInit160 == N = 160

Init == TRUE
Next == TRUE

Id(x) == x

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

\* Equivalent to MkSeq(N, LET F(x) == f[x] IN F), if 1..N \subseteq DOMAIN f
\* @type: (Int -> b) => Seq(b);
SeqFromFun(f) ==
  LET 
    \* @type: (Seq(b), Int) => Seq(b);
    extend(s, x) == Append(s, f[x])
    \* @type: () => Seq(b);
    emptySeq == <<>>
  IN
    ApaFoldSeqLeft(extend, emptySeq, MkSeq(N, Id))


Inv == 
  LET range == 1..N
  IN
  /\ RemakeSet(range) = range
  /\ IncrementalFnChange([x \in range |-> x]) = [x \in range |-> x + 1]
  /\ IncrementalFnBuild(range, Id) = [ x \in range |-> Id(x) ]
  /\ LET 
      f == [x \in range |-> 2 * x]
      F(x) == f[x]
     IN SeqFromFun(f) = MkSeq(N, F)

====