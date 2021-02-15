----------- MODULE LocalInstanceClash576 -------------
(* This is a test for the issue #576.
   A LOCAL INSTANCE should not lead to name collision.  *)
------------------ MODULE inst -----------------------
Foo(x) ==
    LET msg == x IN
    msg
======================================================

LOCAL INSTANCE inst

Bar(x) ==
  LET msg == 3 IN
  Foo(x)

======================================================
