------------------------------ MODULE bcastFolklore_trace ------------------------------

(* An encoding of a parameterized model of the reliable broadcast by message diffusion [1]
	 with crashed failures in TLA+. This broadcast algorithm is described in Fig. 4 of [1].

	 [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors for reliable
	 distributed systems." Journal of the ACM (JACM) 43.2 (1996): 225-267.

	 A short description of the parameterized model is described in:

	 [2] Gmeiner, Annu, et al. "Tutorial on parameterized model checking of fault-tolerant
	 distributed algorithms." International School on Formal Methods for the Design of
	 Computer, Communication and Software Systems. Springer International Publishing, 2014.

	 Igor Konnov, Thanh Hai Tran, Josef Widder, 2016

	 This file is a subject to the license that is bundled together with this package and
	 can be found in the file LICENSE.
 *)

EXTENDS Naturals, Sequences, Apalache (*, FiniteSets *)

CONSTANTS
		\* @type: Int;
		N,
		\* @type: Int;
		T,
		\* @type: Int;
		F,
		\* @type: Bool;
		LoopExists

CInit ==
		/\ N = 5
		/\ T = 2
		/\ F = 2
		/\ LoopExists \in {TRUE, FALSE}

VARIABLES
		\* @typeAlias: STATE = [ Corr: Set(Int), nCrashed: Int, pc: Int -> Str, rcvd:  Int -> Set(<<Int, Str>>), sent: Set(<<Int, Str>>), LoopSelector: Bool, InLoop: Bool];
		\* @type: Set(Int);
		Corr,           (* a set of correct processes *)
		\* @type: Int;
		nCrashed,       (* a number of crashed processes *)
		\* @type: Int -> Str;
		pc,             (* program counters *)
		\* @type: Int -> Set(<<Int, Str>>);
		rcvd,           (* the messages received by each process *)
		\* @type: Set(<<Int, Str>>);
		sent,           (* the messages sent by all correct processes *)

		\* Auxiliary variables
		\* @type: Bool;
		LoopSelector,

		\* @type: Bool;
		InLoop


ASSUME (N > 2 * T) /\ (T >= F) /\ (F >= 0)

Proc == {x \in 0..N: 1 <= x}                  (* all processess, including the faulty ones    *)
M == { "ECHO" }                 (* only ECHO messages are sent in this encoding *)

vars == << pc, rcvd, sent, nCrashed, Corr >>         (* a new variable Corr  *)

AuxInit ==
		/\ LoopSelector \in {TRUE, FALSE}
		/\ InLoop <=> LoopSelector

Init ==
	/\ nCrashed = 0                       (* Initially, there is no crashed process
																					 or all processes are correct. *)
	/\ Corr = Proc
	/\ sent = {}                          (* No messages are sent. *)
	/\ pc \in [ Proc -> {"V0", "V1"} ]    (* If process p received an INIT message,
																					 process p is initialized with V1. Otherwise,
																					 it is initialized with V0. *)
	/\ rcvd = [ i \in Proc |-> {} ]       (* No messages are received. *)
	/\ AuxInit


InitNoBcast ==
	/\ nCrashed = 0                       (* Initially, there is no crashed process
																					 or all processes are correct. *)
	/\ Corr = Proc
	/\ sent = {}                          (* No messages are sent. *)
	/\ pc = [ p \in Proc |-> "V0" ]       (* Nothing is broadcasted and
																					 no process receives an INIT message. *)
	/\ rcvd = [ i \in Proc |-> {} ]       (* No messages are received. *)
	/\ AuxInit

Receive(self) ==                        (* a correct process self receives new messages *)
	/\ pc[self] # "CR"
	/\ \E msgs \in SUBSET (Proc \times M):   (* msgs is a set of messages which has been received  *)
				/\ msgs \subseteq sent
				/\ rcvd[self] \subseteq msgs
				/\ rcvd' = [rcvd EXCEPT ![self] = msgs ]

(* If a correct process received an INIT message or was initialized with V1,
	 it accepts this message and then broadcasts ECHO to all.
 *)
UponV1(self) ==
	/\ pc[self] = "V1"
	/\ pc' = [pc EXCEPT ![self] = "AC"]
	/\ sent' = sent \cup { <<self, "ECHO">> }
	/\ nCrashed' = nCrashed
	/\ Corr' = Corr

(* If a correct process received an ECHO messageaccepts, it accepts and then
	 broadcasts ECHO to all.  *)
UponAccept(self) ==
	/\ (pc[self] = "V0" \/ pc[self] = "V1")
	/\ rcvd'[self] # {}
	/\ pc' = [pc EXCEPT ![self] = "AC"]
	/\ sent' = sent \cup { <<self, "ECHO">> }
	/\ nCrashed' = nCrashed
	/\ Corr' = Corr

(* If a number of crashed processes is less than F, some correct process may crash. *)
UponCrash(self) ==
	/\ nCrashed < F
	/\ pc[self] # "CR"
	/\ nCrashed' = nCrashed + 1
	/\ pc' = [pc EXCEPT ![self] = "CR"]
	/\ sent' = sent
	/\ Corr' = Corr \ { self }

(* A process can receive messages, broadcast ECHO to all, accept or become a crashed one *)
Step(self) ==
	/\ Receive(self)
	/\ \/ UponV1(self)
		 \/ UponAccept(self)
		 \/ UponCrash(self)
		 \/ UNCHANGED << pc, sent, nCrashed, Corr >>

AuxNext ==
	/\ LoopSelector' \in {TRUE, FALSE}
	/\ InLoop => LoopSelector' = FALSE
	/\ InLoop' = (LoopSelector' \/ InLoop)

(* the transition step *)
Next ==  (\E self \in Corr: Step(self)) /\ AuxNext

(* Add the weak fairness condition since we want to check the liveness condition. *)
Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E self \in Corr:    /\ Receive(self)
                                        /\  \/ UponV1(self)
                                            \/ UponAccept(self)
                                            \/ UNCHANGED << pc, sent, nCrashed, Corr >> )


SpecNoBcast == InitNoBcast /\ [][Next]_vars
													 /\ WF_vars(\E self \in Corr: /\ Receive(self)
																												/\ \/ UponV1(self)
																													 \/ UponAccept(self)
																													 \/ UNCHANGED << pc, sent, nCrashed, Corr >> )

(* V0 - a process did not received an INIT message
	 V1 - a process received an INIT message
	 AC - a process accepted and sent the message to everybody
	 CR - a process is crashed
 *)
TypeOK ==
	/\ sent \in SUBSET (Proc \times M)
	/\ pc \in [ Proc -> {"V0", "V1", "AC", "CR"} ]
	/\ rcvd \in [ Proc -> SUBSET (Proc \times M) ]
	/\ nCrashed \in {x \in Nat: 0 <= x /\ x <= N}
	/\ Corr \in SUBSET Proc

\* @type: Seq(STATE) => Bool;
LoopOK(hist) ==
	LET lastState == hist[Len(hist)] IN
	/\ LET \* @type: (Bool, STATE) => Bool;
			SelectorVariablesMatch(acc, state) ==
				/\ acc
				/\ state.LoopSelector =>
						/\ state.Corr = lastState.Corr
						/\ state.nCrashed = lastState.nCrashed
						/\ state.pc = lastState.pc
						/\ state.rcvd = lastState.rcvd
						/\ state.sent = lastState.sent IN
			ApaFoldSeqLeft(SelectorVariablesMatch, TRUE, hist)
	/\ LoopExists => lastState.InLoop

(* If no correct process does not broadcast then no correct processes accepts. *)
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] /= "AC")

\* @type: Seq(STATE) => Bool;
UnforgTrace(hist) ==
	 LoopOK(hist) =>
        LET firstState == hist[1] IN
            LET \* @type: (Bool, STATE) => Bool;
                AllNotAC(acc, state) == acc /\ \A i \in state.Corr: state.pc[i] /= "AC" IN
                (\A i \in firstState.Corr: firstState.pc[i] = "V0") => ApaFoldSeqLeft(AllNotAC, TRUE, hist)

(* Unforg is correct iff the initial state is InitNoBcast. *)
Unforg == (\A self \in Corr: (pc[self] /= "AC"))

(* If a correct process broadcasts, then every correct process eventually accepts. *)
CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\E i \in Corr: pc[i] = "AC")

\* @type: Seq(STATE) => Bool;
CorrTrace(hist) ==
  LoopOK(hist) =>
  LET firstState == hist[1] IN
      LET \* @type: (Bool, STATE) => Bool;
          EventuallyExistsAC(acc, state) ==
          acc \/ \E i \in state.Corr: state.pc[i] /= "AC" IN
              (\A i \in firstState.Corr: firstState.pc[i] = "V1") => ApaFoldSeqLeft(EventuallyExistsAC, FALSE, hist)

(* If a correct process accepts, then every correct process eventually accepts.  *)
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))


\* @type: Seq(STATE) => Bool;
RelayTrace(hist) ==
	LET LoopStartIndex == CHOOSE x \in DOMAIN hist: hist[x].LoopSelector IN
	LET range(a,b) == {x \in DOMAIN hist: a <= x /\ x <= b } IN
	 LoopOK(hist) =>
		\A step \in DOMAIN hist:
			LET curState == hist[step] IN
			(\E i \in curState.Corr: curState.pc[i] = "AC")
				=> \E otherStep \in range((IF step < LoopStartIndex \/ ~LoopExists THEN step ELSE LoopStartIndex), Len(hist)):
					LET otherState == hist[otherStep] IN
							\A i \in otherState.Corr: otherState.pc[i] = "AC"


(* If a message is sent by a correct process, then every correct processes eventually
	 receives this message. *)
ReliableChan ==
	[]( \E sndr \in {x \in Nat: 1 <= x /\ x <= N} : (<<sndr, "ECHO">> \in sent
														=> <>[](\A p \in Corr : <<sndr, "ECHO">> \in rcvd[p])))

\* @type: Seq(STATE) => Bool;
ReliableTrace(hist) ==
    LET LoopStartIndex == CHOOSE x \in DOMAIN hist: hist[x].LoopSelector IN
    LET range(a,b) == {x \in DOMAIN hist: a <= x /\ x <= b } IN
        LoopExists /\ LoopOK(hist) =>
            \A step \in DOMAIN hist: LET curState == hist[step] IN \E sndr \in 1..N : (<<sndr, "ECHO">> \in curState.sent
                => (\E step2 \in range((IF step < LoopStartIndex \/ ~LoopExists THEN step ELSE LoopStartIndex), Len(hist)):
                    \A step3 \in range((IF step2 < LoopStartIndex \/ ~LoopExists THEN step2 ELSE LoopStartIndex), Len(hist)):
                        \A p \in hist[step3].Corr : <<sndr, "ECHO">> \in hist[step3].rcvd[p]))

\* @type: Seq(STATE) => Bool;
Fairness(hist) ==
    LET LoopStartIndex == CHOOSE x \in DOMAIN hist: hist[x].LoopSelector IN
    LET range(a,b) == {x \in DOMAIN hist: a <= x /\ x <= b } IN
    \A step \in range(LoopStartIndex, Len(hist)):
        LET nextStep == IF step = Len(hist) THEN LoopStartIndex ELSE step + 1 IN
        /\ ~\E p \in hist[step].Corr:   \/      /\ (hist[step].pc[p] = "V0" \/ hist[step].pc[p] = "V1")
                                                /\ hist[nextStep].rcvd[p] # {}
                                        \/  hist[step].pc[p] = "V1"
                                        \/  hist[step].pc[p] \notin {"CR", "AC"}

Property(hist) ==
    Fairness(hist) => CorrTrace(hist)

=============================================================================
\* Modification History
\* Last modified Mon Sep 03 17:01:26 CEST 2018 by tthai
