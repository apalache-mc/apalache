--------------------------- MODULE 09_OutTransition ---------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

VARIABLE
  (*
    @type: Int;
  *)
  year

VARIABLE
  (*
    @type: Bool;
  *)
  hasLicense

(*
  @type: (() => Bool);
*)
ASSUME(80 \in 0 .. 99)

(*
  @type: (() => Bool);
*)
ASSUME(18 \in 1 .. 99)

(*
  @type: (() => Bool);
*)
Init_si_0000 == year' := 80 /\ hasLicense' := FALSE

(*
  @type: (() => Bool);
*)
Next_si_0000 == year' := ((year + 1) % 100) /\ hasLicense' := hasLicense

(*
  @type: (() => Bool);
*)
Next_si_0001 == year - 80 >= 18 /\ hasLicense' := TRUE /\ year' := year

================================================================================
