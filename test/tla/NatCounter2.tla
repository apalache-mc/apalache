---------------------------- MODULE NatCounter2 ----------------------------
EXTENDS Naturals

VARIABLE x

Init ==
    x \in { a - b: a, b \in Nat } 

=============================================================================
\* Modification History
\* Last modified Wed Aug 05 19:17:32 CEST 2020 by igor
\* Created Wed Aug 05 19:16:49 CEST 2020 by igor
