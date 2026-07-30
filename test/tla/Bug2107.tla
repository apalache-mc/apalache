--------------------------- MODULE Bug2107 ---------------------------
\* Regression for https://github.com/apalache-mc/apalache/issues/2107
\*
\* Verbatim minimal repro from
\*   https://github.com/apalache-mc/apalache/issues/2107#issuecomment-2772817347
\* contributed by @rodrigo7491.  Used to crash with
\*   java.lang.ClassCastException:
\*     class at.forsyte.apalache.tla.lir.BoolT1$ cannot be cast to
\*     class at.forsyte.apalache.tla.lir.FunT1
\* at FunCtorRule.apply, because Flatten dropped the typeTag of the
\* function constructor when its body's nested `/\` got flattened.

VARIABLES
    \* @type: Int -> Bool;
    flag

Init == flag = [p \in {1} |-> FALSE]

Next == flag' = [p \in {1} |-> IF TRUE /\ TRUE /\ TRUE THEN FALSE ELSE FALSE]

P1 == <>(TRUE)
P2 == [](TRUE)
P3 == TRUE

=============================================================================
