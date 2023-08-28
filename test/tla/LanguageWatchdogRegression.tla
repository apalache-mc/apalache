---------------------------- MODULE LanguageWatchdogRegression --------------------------

EXTENDS Integers, Apalache


\* @type: Set(Int);
GEN == Gen(1)

Init == 0 \in GEN
Next == TRUE
Inv == TRUE
=================================================================