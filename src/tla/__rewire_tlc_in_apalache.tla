---------------------------- MODULE TLC ----------------------------
(**
 * ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 * We have to call this module TLC in any case, otherwise, SANY complains.
 *
 * This file contains alternative definitions for the TLC operators.
 * Most importantly, we are adding type annotations. We also define the
 * Apalache-compatible behavior. The majority of these operators
 * are imperative, so we define stubs for these operators, as they are
 * incompatible with symbolic execution.
 *
 * These definitions are automatically rewired by the Apalache importer.
 *
 * Compare with the original definitions in TLC.tla:
 *
 * https://github.com/tlaplus/tlaplus/blob/9310ee79efbebc700c4b84e8b805c35ab20161bb/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/TLC.tla
 *)

LOCAL INSTANCE Naturals 

\* The famous smiley operator.
\*
\* @type: (a, b) => (a -> b);
key :> value ==
    [ x \in { key } |-> value ]

\* Function composition (fun-fun).
\* 
\* @type: (a -> b, a -> b) => (a -> b);
f1 @@ f2 == 
    \* cache f1, f2, and the domains, Apalache would not inline them
    LET __f1 == f1
        __f2 == f2
    IN
    LET __d1 == DOMAIN __f1
        __d2 == DOMAIN __f2
    IN
    [x \in __d1 \union __d2 |->
            IF x \in __d1
            THEN __f1[x]
            ELSE __f2[x]]

\* Print is doing nothing in Apalache.
\* 
\* @type: (Str, a) => a;
Print(out, val) == val

\* Print is doing nothing in Apalache.
\*
\* @type: Str => Bool;
PrintT(out) == TRUE

\* In Apalache, assert is side-effect free.
\* It never produces an error, even if the condition is false.
\*
\* @type: (Bool, Str) => Bool;
Assert(cond, out) ==
    cond

\* Apalache does not support this operator, but the type checker does.
\*
\* @type: () => Int;
JavaTime ==
    \* deliberately return a non-standard value,
    \* as we cannot produce current time in a symbolic execution
    123

\* Apalache does not support this operator, but the type checker does.
\*
\* @type: Int => a;
TLCGet(i) ==
    LET \* @type: () => Set(a);
        Empty == {}
    IN
    CHOOSE x \in Empty: TRUE
    

\* Apalache does not support this operator, but the type checker does.
\*
\* @type: (Int, a) => Bool;
TLCSet(i, v) ==
    TRUE

\* @type: Set(a) => Set(a -> a);
Permutations(S) == 
   \* exactly the same behavior as in TLC.tla
   {f \in [S -> S] : \A w \in S : \E v \in S : f[v] = w}

\* We return the function instead of a sequence, because that is what it returns.
\*
\* @type: (Seq(a), (a, a) => Bool) => (Int -> a);
SortSeq(s, Op(_, _)) ==
    \* Similar to that of TLC!SortSeq, but using (DOMAIN s) instead of 1..Len(s)
    LET Perm == CHOOSE p \in Permutations(DOMAIN s):
                  \A i, j \in DOMAIN s: 
                     (i < j) => Op(s[p[i]], s[p[j]]) \/ (s[p[i]] = s[p[j]])
    IN  [i \in DOMAIN s |-> s[Perm[i]]]

\* Obviously, we cannot do randomization in Apalache.
\*
\* @type: Set(a) => a;
RandomElement(s) ==
    CHOOSE x \in s : TRUE

\* Most likely, the type checker will fail on that one more often than it will work.
\*
\* @type: () => a;
Any ==
    LET \* @type: () => Set(a);
        Empty == {}
    IN
    CHOOSE x \in Empty: TRUE

\* @type: a => Str;
ToString(v) == ""

\* For type compatibility with TLC.
\*
\* @type: a => a;
TLCEval(v) == v

===============================================================================
