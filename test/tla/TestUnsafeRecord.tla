--------------------------- MODULE TestUnsafeRecord ---------------------------
\* the record in R has the type { name: Str, a: Int}
R == [name |-> "A", a |-> 3]

\* the type checker will report a type error in UnsafeAccess
UnsafeAccess == R.b
===============================================================================
