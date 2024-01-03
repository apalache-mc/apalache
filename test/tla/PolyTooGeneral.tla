---------------------- MODULE PolyTooGeneral ------------------------------
\* A library author did not think carefully about the types
\* and wrote a too general type. The type checker should complain.
\*
\* @type: a => b;
Id(x) == x
===========================================================================
