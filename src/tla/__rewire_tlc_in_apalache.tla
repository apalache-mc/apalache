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
__key :> __value ==
    [ __x \in { __key } |-> __value ]

\* Function composition (fun-fun).
\* 
\* @type: (a -> b, a -> b) => (a -> b);
__f1 @@ __f2 == 
    \* cache f1, f2, and the domains, Apalache would not inline them
    LET __f1_cache == __f1
        __f2_cache == __f2
    IN
    LET __d1 == DOMAIN __f1_cache
        __d2 == DOMAIN __f2_cache
    IN
    [__x \in __d1 \union __d2 |->
            IF __x \in __d1
            THEN __f1_cache[__x]
            ELSE __f2_cache[__x]]

\* Print is doing nothing in Apalache.
\* 
\* @type: (a, b) => b;
Print(__out, __val) == 
    __val

\* Print is doing nothing in Apalache.
\*
\* @type: a => Bool;
PrintT(__out) == 
    TRUE

\* In Apalache, assert is side-effect free.
\* It never produces an error, even if the condition is false.
\*
\* @type: (Bool, Str) => Bool;
Assert(__cond, __out) == 
    __cond

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
TLCGet(__i) ==
    LET \* @type: () => Set(a);
        __Empty == {}
    IN
    CHOOSE __x \in __Empty: TRUE
    

\* Apalache does not support this operator, but the type checker does.
\*
\* @type: (Int, a) => Bool;
TLCSet(__i, __v) ==
    TRUE

\* @type: Set(a) => Set(a -> a);
Permutations(__S) == 
   \* exactly the same behavior as in TLC.tla
   {__f \in [__S -> __S] : \A __w \in __S : \E __v \in __S : __f[__v] = __w}

\* We return the function instead of a sequence, because that is what it returns.
\*
\* @type: (Seq(a), (a, a) => Bool) => (Int -> a);
SortSeq(__s, __Op(_, _)) ==
    \* Similar to that of TLC!SortSeq, but using (DOMAIN s) instead of 1..Len(s)
    LET __Perm == CHOOSE __p \in Permutations(DOMAIN __s):
        \A __i, __j \in DOMAIN __s: 
            \/ (__i < __j) => __Op(__s[__p[__i]], __s[__p[__j]]) 
            \/ (__s[__p[__i]] = __s[__p[__j]])
    IN  [__i \in DOMAIN __s |-> __s[__Perm[__i]]]

\* Obviously, we cannot do randomization in Apalache.
\*
\* @type: Set(a) => a;
RandomElement(__s) ==
    CHOOSE __x \in __s : TRUE

\* Most likely, the type checker will fail on that one more often than it will work.
\*
\* @type: () => a;
Any ==
    LET \* @type: () => Set(a);
        __Empty == {}
    IN
    CHOOSE __x \in __Empty: TRUE

\* @type: a => Str;
ToString(__v) == ""

\* For type compatibility with TLC.
\*
\* @type: a => a;
TLCEval(__v) == __v

===============================================================================
