----------- MODULE AnnotationsAndInstances592 --------------
(* A regression test for the issue #592 *)
---- MODULE Utils ----
\* @type: (Int -> Int) => Int;
Foo(f) ==
    f[1]
======================

---- MODULE UserA ----
EXTENDS Utils
Bar(f) == Foo(f)
======================

---- MODULE UserB ----
INSTANCE Utils
Baz(f) == Foo(f)
======================

---- MODULE UserC ----
INSTANCE UserA
======================

INSTANCE UserA

B == INSTANCE UserB

INSTANCE UserC

============================================================
