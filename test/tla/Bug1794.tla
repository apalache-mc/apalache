-------------------------------- MODULE Bug1794 --------------------------------
\* This is a regression test
\* for assumptions over non-CONSTANT values
\*
\* https://github.com/apalache-mc/apalache/issues/1794

EXTENDS Integers

Init == TRUE
Next == TRUE

A == 9

ASSUME( A > 0 )

===============================================================================
