-------------------------------- MODULE y2k --------------------------------
(*
 * A simple specification of a year counter that is subject to the Y2K problem.
 * In this specification, a registration office keeps records of birthdays and
 * issues driver's licenses. As usual, a person may get a license, if they
 * reached a certain age, e.g., age of 18. The software engineers never thought
 * of their program being used until the next century, so they stored the year
 * of birth using only two digits (who would blame them, the magnetic tapes
 * were expensive!). The new millenium came with new bugs.
 *
 * This is a made up example, not reflecting any real code.
 * To learn more about Y2K, check: https://en.wikipedia.org/wiki/Year_2000_problem
 *
 * Igor Konnov, January 2020
 *)

EXTENDS Integers
 
CONSTANT BIRTH_YEAR,    \* the year to start with, between 0 and 99
         LICENSE_AGE    \* the minimum age to obtain a license
         
ASSUME(BIRTH_YEAR \in 0..99)              
ASSUME(LICENSE_AGE \in 1..99)              
 
VARIABLE year, hasLicense

Age == year - BIRTH_YEAR 

Init ==
    /\ year = BIRTH_YEAR
    /\ hasLicense = FALSE
    
NewYear ==
    /\ year' = (year + 1) % 100 \* the programmers decided to use two digits
    /\ UNCHANGED hasLicense
    
IssueLicense ==
    /\ Age >= LICENSE_AGE
    /\ hasLicense' = TRUE
    /\ UNCHANGED year
    
Next ==
    \/ NewYear
    \/ IssueLicense

\* The somewhat "obvious" invariant, which is violated    
Safety ==
    hasLicense => (Age >= LICENSE_AGE)

\* This is probably the only invariant we can formulate, usually, it is called TypeOK    
Inv ==
    /\ year \in 0..99
    /\ hasLicense \in BOOLEAN

=============================================================================
\* Modification History
\* Last modified Tue Jan 07 20:18:12 CET 2020 by igor
\* Created Fri Jan 03 12:51:52 CET 2020 by igor
