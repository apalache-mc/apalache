----------- MODULE LocalDefClash576 -------------
(* This is a test for the issue #576.
   A LOCAL operator definition should not lead to name collision.  *)
LOCAL Foo(x) ==
    LET msg == x IN
    msg

Bar(x) ==
  LET msg == 3 IN
  \* SANY importer inlines the definition of Foo as a LET-IN definition,
  \* which makes msg introduced twice. The importer should produce
  \* a unique scope to avoid that.
  Foo(x)

Baz(x) ==
  LET msg == 4 IN
  \* two instantiations should not produce an error
  <<Foo(x), Foo(x)>>

======================================================
