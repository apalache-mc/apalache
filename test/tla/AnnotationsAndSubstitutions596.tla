--------- MODULE AnnotationsAndSubstitutions596 ------------
(* A regression test for the issue #596 *)
---- MODULE Utils ----
VARIABLE myArr

Foo(f) ==
    LET \* @type: (Int -> Int) => Int;
        X(g) == g[1]
    IN
    X(f)

Get ==
    myArr[1]

======================

VARIABLE
    \* @type: Int -> Int;
    arr

U == INSTANCE Utils WITH myArr <- arr

Init ==
    arr = [ i \in {0, 1} |-> i ]

Next ==
    arr' = arr

============================================================
