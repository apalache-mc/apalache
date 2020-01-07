---------------------------- MODULE y2k_instance ----------------------------
(*
 * Another way to instantiate constants for apalache is to
 * use INSTANCE.
 *)
 
VARIABLE year, hasLicense

INSTANCE y2k WITH BIRTH_YEAR <- 80, LICENSE_AGE <- 18

=============================================================================
\* Modification History
\* Last modified Tue Jan 07 11:24:55 CET 2020 by igor
\* Created Tue Jan 07 11:16:18 CET 2020 by igor
