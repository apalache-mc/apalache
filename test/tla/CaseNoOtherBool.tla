-------------------------- MODULE CaseNoOtherBool ------------------------------
\* a regression test for issue #285
VARIABLE
    \* @type: Int;
    x

Init ==
    x = 0 \/ x = 1

Next ==
    CASE x = 0 -> x' = 1
      [] x = 1 -> x' = 2
      [] x = 2 -> x' = 0

===============================================================================
