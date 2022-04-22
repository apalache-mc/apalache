---------------------------- MODULE counterexample ----------------------------

EXTENDS bcastFolklore_trace

(* Constant initialization state *)
ConstInit == F = 2/\ LoopExists = TRUE/\ N = 5/\ T = 2

(* Initial state *)
State0 ==
  Corr = { 1, 2, 3, 4, 5 }
    /\ F = 2
    /\ InLoop = FALSE
    /\ LoopExists = TRUE
    /\ LoopSelector = FALSE
    /\ N = 5
    /\ T = 2
    /\ nCrashed = 0
    /\ pc
      = SetAsFun({ <<1, "V1">>,
        <<2, "V0">>,
        <<3, "V1">>,
        <<5, "V1">>,
        <<4, "V1">> })
    /\ rcvd
      = SetAsFun({ <<1, {}>>, <<2, {}>>, <<3, {}>>, <<5, {}>>, <<4, {}>> })
    /\ sent = {}

(* Transition 0 to State1 *)
State1 ==
  Corr = { 1, 2, 3, 4, 5 }
    /\ F = 2
    /\ InLoop = FALSE
    /\ LoopExists = TRUE
    /\ LoopSelector = FALSE
    /\ N = 5
    /\ T = 2
    /\ nCrashed = 0
    /\ pc
      = SetAsFun({ <<1, "V1">>,
        <<2, "V0">>,
        <<3, "V1">>,
        <<5, "V1">>,
        <<4, "AC">> })
    /\ rcvd
      = SetAsFun({ <<1, {}>>, <<2, {}>>, <<3, {}>>, <<5, {}>>, <<4, {}>> })
    /\ sent = {<<4, "ECHO">>}

(* Transition 1 to State2 *)
State2 ==
  Corr = { 1, 2, 3, 4, 5 }
    /\ F = 2
    /\ InLoop = FALSE
    /\ LoopExists = TRUE
    /\ LoopSelector = FALSE
    /\ N = 5
    /\ T = 2
    /\ nCrashed = 0
    /\ pc
      = SetAsFun({ <<1, "AC">>,
        <<2, "V0">>,
        <<3, "V1">>,
        <<5, "V1">>,
        <<4, "AC">> })
    /\ rcvd
      = SetAsFun({ <<1, {<<4, "ECHO">>}>>,
        <<2, {}>>,
        <<3, {}>>,
        <<5, {}>>,
        <<4, {}>> })
    /\ sent = { <<1, "ECHO">>, <<4, "ECHO">> }

(* Transition 1 to State3 *)
State3 ==
  Corr = { 1, 2, 3, 4, 5 }
    /\ F = 2
    /\ InLoop = FALSE
    /\ LoopExists = TRUE
    /\ LoopSelector = FALSE
    /\ N = 5
    /\ T = 2
    /\ nCrashed = 0
    /\ pc
      = SetAsFun({ <<1, "AC">>,
        <<2, "AC">>,
        <<3, "V1">>,
        <<5, "V1">>,
        <<4, "AC">> })
    /\ rcvd
      = SetAsFun({ <<1, {<<4, "ECHO">>}>>,
        <<2, {<<4, "ECHO">>}>>,
        <<3, {}>>,
        <<5, {}>>,
        <<4, {}>> })
    /\ sent = { <<1, "ECHO">>, <<2, "ECHO">>, <<4, "ECHO">> }

(* Transition 0 to State4 *)
State4 ==
  Corr = { 1, 2, 3, 4, 5 }
    /\ F = 2
    /\ InLoop = FALSE
    /\ LoopExists = TRUE
    /\ LoopSelector = FALSE
    /\ N = 5
    /\ T = 2
    /\ nCrashed = 0
    /\ pc
      = SetAsFun({ <<1, "AC">>,
        <<2, "AC">>,
        <<3, "AC">>,
        <<5, "V1">>,
        <<4, "AC">> })
    /\ rcvd
      = SetAsFun({ <<1, {<<4, "ECHO">>}>>,
        <<2, {<<4, "ECHO">>}>>,
        <<3, {<<1, "ECHO">>}>>,
        <<5, {}>>,
        <<4, {}>> })
    /\ sent = { <<1, "ECHO">>, <<2, "ECHO">>, <<3, "ECHO">>, <<4, "ECHO">> }

(* Transition 0 to State5 *)
State5 ==
  Corr = { 1, 2, 3, 4, 5 }
    /\ F = 2
    /\ InLoop = TRUE
    /\ LoopExists = TRUE
    /\ LoopSelector = TRUE
    /\ N = 5
    /\ T = 2
    /\ nCrashed = 0
    /\ pc
      = SetAsFun({ <<1, "AC">>,
        <<2, "AC">>,
        <<3, "AC">>,
        <<5, "AC">>,
        <<4, "AC">> })
    /\ rcvd
      = SetAsFun({ <<1, {<<4, "ECHO">>}>>,
        <<2, {<<4, "ECHO">>}>>,
        <<3, {<<1, "ECHO">>}>>,
        <<5, {}>>,
        <<4, {}>> })
    /\ sent
      = { <<1, "ECHO">>,
        <<2, "ECHO">>,
        <<3, "ECHO">>,
        <<4, "ECHO">>,
        <<5, "ECHO">> }

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  LET Call_hist ==
    <<
      [LoopExists |-> $C$13,
        N |-> $C$6,
        T |-> $C$7,
        LoopSelector |-> $C$91,
        F |-> $C$7,
        pc |-> $C$46,
        Corr |-> $C$32,
        sent |-> $C$33,
        nCrashed |-> $C$21,
        rcvd |-> $C$86,
        InLoop |-> $C$91], [LoopExists |-> $C$13,
        N |-> $C$6,
        T |-> $C$7,
        LoopSelector |-> $C$432,
        F |-> $C$7,
        pc |-> $C$452,
        Corr |-> $C$454,
        sent |-> $C$453,
        nCrashed |-> $C$431,
        rcvd |-> $C$541,
        InLoop |-> $C$455], [LoopExists |-> $C$13,
        N |-> $C$6,
        T |-> $C$7,
        LoopSelector |-> $C$1407,
        F |-> $C$7,
        pc |-> $C$1427,
        Corr |-> $C$1431,
        sent |-> $C$1428,
        nCrashed |-> $C$1406,
        rcvd |-> $C$1524,
        InLoop |-> $C$1432], [LoopExists |-> $C$13,
        N |-> $C$6,
        T |-> $C$7,
        LoopSelector |-> $C$2393,
        F |-> $C$7,
        pc |-> $C$2413,
        Corr |-> $C$2417,
        sent |-> $C$2414,
        nCrashed |-> $C$2392,
        rcvd |-> $C$2510,
        InLoop |-> $C$2418], [LoopExists |-> $C$13,
        N |-> $C$6,
        T |-> $C$7,
        LoopSelector |-> $C$3379,
        F |-> $C$7,
        pc |-> $C$3399,
        Corr |-> $C$3403,
        sent |-> $C$3400,
        nCrashed |-> $C$3378,
        rcvd |-> $C$3496,
        InLoop |-> $C$3404], [LoopExists |-> $C$13,
        N |-> $C$6,
        T |-> $C$7,
        LoopSelector |-> $C$4365,
        F |-> $C$7,
        pc |-> $C$4385,
        Corr |-> $C$4397,
        sent |-> $C$4386,
        nCrashed |-> $C$4364,
        rcvd |-> $C$4490,
        InLoop |-> $C$4398]
    >>
  IN
  LET LoopStartIndex_si_3 ==
      CHOOSE x$13 \in DOMAIN Call_hist: (Call_hist)[x$13]["LoopSelector"]
    IN
    \A step$3 \in {
      x$14 \in DOMAIN Call_hist:
        LoopStartIndex_si_3 <= x$14 /\ x$14 <= Len((Call_hist))
    }:
      LET nextStep_si_2 ==
        IF step$3 = Len((Call_hist)) THEN LoopStartIndex_si_3 ELSE step$3 + 1
      IN
      \A p$3 \in (Call_hist)[step$3]["Corr"]:
        ((~((Call_hist)[step$3]["pc"][p$3] = "V0")
              /\ ~((Call_hist)[step$3]["pc"][p$3] = "V1"))
            \/ (Call_hist)[(nextStep_si_2)]["rcvd"][p$3] = {})
          /\ ~((Call_hist)[step$3]["pc"][p$3] = "V1")
          /\ (Call_hist)[step$3]["pc"][p$3] \in { "CR", "AC" }
    /\ LET LoopStartIndex_si_4 ==
      CHOOSE x$15 \in DOMAIN Call_hist: (Call_hist)[x$15]["LoopSelector"]
    IN
    (LoopExists
        /\ LET lastState_si_2 == (Call_hist)[(Len((Call_hist)))] IN
        ApaFoldSeqLeft(LET t_3_si_2(acc_si_2, state_si_2) ==
            acc$2
              /\ (~(state$2["LoopSelector"])
                \/ (state$2["Corr"] = (lastState_si_2)["Corr"]
                  /\ state$2["nCrashed"] = (lastState_si_2)["nCrashed"]
                  /\ state$2["pc"] = (lastState_si_2)["pc"]
                  /\ state$2["rcvd"] = (lastState_si_2)["rcvd"]
                  /\ state$2["sent"] = (lastState_si_2)["sent"]))
          IN
          t_3$2, TRUE, (Call_hist))
          /\ (~LoopExists \/ (lastState_si_2)["InLoop"]))
      /\ Skolem((\E step$4 \in DOMAIN Call_hist:
        LET curState_si_2 == (Call_hist)[step$4] IN
        \A sndr$2 \in 1 .. 5:
          <<sndr$2, "ECHO">> \in (curState_si_2)["sent"]
            /\ (\A step2$2 \in {
              x$16 \in DOMAIN Call_hist:
                (IF step$4 < LoopStartIndex_si_4 \/ ~LoopExists
                  THEN step$4
                  ELSE LoopStartIndex_si_4)
                    <= x$16
                  /\ x$16 <= Len((Call_hist))
            }:
              Skolem((\E x$17 \in DOMAIN Call_hist:
                ((IF step2$2 < LoopStartIndex_si_4 \/ ~LoopExists
                    THEN step2$2
                    ELSE LoopStartIndex_si_4)
                      <= x$17
                    /\ x$17 <= Len((Call_hist)))
                  /\ Skolem((\E p$4 \in (Call_hist)[x$17]["Corr"]:
                    ~(<<sndr$2, "ECHO">> \in (Call_hist)[x$17]["rcvd"][p$4]))))))))

================================================================================
(* Created by Apalache on Thu Apr 21 11:17:10 CEST 2022 *)
(* https://github.com/informalsystems/apalache *)
