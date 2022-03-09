--------------- MODULE TestHash2 --------------
\* Run Apalache to check the invariant for all combinations of hashes
\*
\* apalache-mc check --cinit=ConstInit --inv=Inv TestHash2.tla
EXTENDS Integers

BitString == [1..6 -> {0,1}]

AllowedStrings == {"a", "b", "c", "d", "e"}

\* @type: (a -> b) => Bool;
IsInjective(f) ==
    \A a,b \in DOMAIN f : f[a] = f[b] => a = b

CONSTANT
    \* @type: Str -> (Int -> Int);
    hash

\* this assumption is redundant when using ConstInit
\* ASSUME hash \in [AllowedStrings -> BitString] /\ IsInjective(hash)

ConstInit ==
    hash \in [AllowedStrings -> BitString] /\ IsInjective(hash)

Init == TRUE

Next == TRUE

Inv == \A x, y \in AllowedStrings:
         x /= y => hash[x] /= hash[y]

==============================================
