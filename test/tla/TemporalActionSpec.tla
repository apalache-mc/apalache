-------------------------- MODULE TemporalActionSpec --------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_1

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_1

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_1_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_2

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_2

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_2_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __FalseLiveness_init

VARIABLE
  (*
    @type: Int;
  *)
  __saved_x

VARIABLE
  (*
    @type: Bool;
  *)
  __InLoop

VARIABLE
  (*
    @type: Int;
  *)
  x

Init ==
  x = 0
    /\ __saved_x = x
    /\ __InLoop = FALSE
    /\ __temporal_t_1 \in BOOLEAN
    /\ __saved___temporal_t_1 = __temporal_t_1
    /\ __temporal_t_2 \in BOOLEAN
    /\ __saved___temporal_t_2 = __temporal_t_2
    /\ __temporal_t_2_unroll = TRUE
    /\ __temporal_t_1_unroll = FALSE
    /\ __FalseLiveness_init = __temporal_t_1

Next ==
  x' = (IF x < 3 THEN x + 1 ELSE 0)
    /\ __InLoop' \in BOOLEAN
    /\ (__InLoop => __InLoop')
    /\ (IF __InLoop = __InLoop' THEN UNCHANGED <<__saved_x>> ELSE __saved_x' = x)
    /\ __temporal_t_1' \in BOOLEAN
    /\ __saved___temporal_t_1'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_1 ELSE __temporal_t_1)
    /\ __temporal_t_2' \in BOOLEAN
    /\ __saved___temporal_t_2'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_2 ELSE __temporal_t_2)
    /\ __temporal_t_2_unroll' \in BOOLEAN
    /\ (__temporal_t_2 <=> (x' = x + 1 \/ x' = x) /\ __temporal_t_2')
    /\ (__temporal_t_2_unroll'
      <=> __temporal_t_2_unroll /\ (~__InLoop' \/ (x' = x + 1 \/ x' = x)'))
    /\ __temporal_t_1_unroll' \in BOOLEAN
    /\ (__temporal_t_1 <=> __temporal_t_2 \/ __temporal_t_1')
    /\ (__temporal_t_1_unroll'
      <=> __temporal_t_1_unroll \/ (__InLoop' /\ __temporal_t_2'))
    /\ UNCHANGED __FalseLiveness_init

(*
  @type: (() => Bool);
*)
__LoopOK ==
  __InLoop
    /\ x = __saved_x
    /\ __temporal_t_1 = __saved___temporal_t_1
    /\ __temporal_t_2 = __saved___temporal_t_2
    /\ (__temporal_t_2_unroll => __temporal_t_2)
    /\ (__temporal_t_1 => __temporal_t_1_unroll)

FalseLiveness == __LoopOK => __FalseLiveness_init

ShowMeALoop ==
    ~__LoopOK

================================================================================
