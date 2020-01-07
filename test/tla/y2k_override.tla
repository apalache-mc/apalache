---------------------------- MODULE y2k_override ----------------------------
(*
 * One way to instantiate constants for apalache is to use the OVERRIDE prefix. 
 *)
 
EXTENDS y2k

OVERRIDE_BIRTH_YEAR == 80
OVERRIDE_LICENSE_AGE == 18

=============================================================================
\* Modification History
\* Last modified Tue Jan 07 11:24:55 CET 2020 by igor
\* Created Tue Jan 07 11:16:18 CET 2020 by igor
