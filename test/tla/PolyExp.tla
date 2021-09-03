-------------------------- MODULE PolyExp -------------------------------------
\* This is the classical example of exponential explosion in
\* let polymorphism, similar to the example by:
\*
\* Mairson, Harry G. Deciding ML typability is complete for 
\* deterministic exponential time. POPL, pp. 382–401. ACM, 1990.

\* @type: (a, b) => <<a, b>>;
Pair(x, y) == <<x, y>>

\* Inferring the type of this operator requires plenty of time and memory.
\* If this one runs out of memory, try to stop at F4 instead of F5.
Exp ==
    LET F0 == [ x \in {} |-> Pair(x, x) ] IN
      LET F1 == [ y \in {} |-> F0[F0[y]] ] IN
        LET F2 == [ y \in {} |-> F1[F1[y]] ] IN
          LET F3 == [ y \in {} |-> F2[F2[y]] ] IN
            LET F4 == [ y \in {} |-> F3[F3[y]] ] IN
              LET F5 == [ y \in {} |-> F4[F4[y]] ] IN
                F5

===============================================================================
