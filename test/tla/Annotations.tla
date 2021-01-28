-------- MODULE Annotations ----------
EXTENDS Integers

CONSTANT
  \* @type("Int")
  N

VARIABLE
  \* @type("Set(Int)")
  set

\* @pure
\* @type("Int => Int")
Inc(n) == n + 1

\* @type("Int => Int")
LOCAL LocalInc(x) == x + 1

A(n) ==
  LET \* @pure
      \* @type("Int => Int")
      Dec(x) == x + 1
  IN
  Dec(n)

RECURSIVE Fact(_)
\* @tailrec
\* @type("Int => Int")
Fact(n) ==
  IF n <= 1 THEN 1 ELSE n * Fact(n - 1)

\* @tailrec
\* @type("Int -> Int")
FactFun[n \in Int] ==
  IF n <= 1 THEN 1 ELSE n * FactFun[n - 1]

======================================
