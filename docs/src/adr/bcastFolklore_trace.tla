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
		\* @typeAlias: STATE = [ Corr: Set(Int), nCrashed: Int, pc: Int -> Str, rcvd:  Int -> Set(<<Int, Str>>), sent: Set(<<Int, Str>>)];
		\* @type: Set(Int);
		Corr,           (* a set of correct processes *)
		\* @type: Int;
		nCrashed,       (* a number of crashed processes *)
		\* @type: Int -> Str;
		pc,             (* program counters *)
		\* @type: Int -> Set(<<Int, Str>>);
		rcvd,           (* the messages received by each process *)
		\* @type: Set(<<Int, Str>>);
		sent           (* the messages sent by all correct processes *)


ASSUME (N > 2 * T) /\ (T >= F) /\ (F >= 0)

Proc == {x \in 0..N: 1 <= x}                  (* all processess, including the faulty ones    *)
M == { "ECHO" }                 (* only ECHO messages are sent in this encoding *)

vars == << pc, rcvd, sent, nCrashed, Corr >>         (* a new variable Corr  *)

Init ==
	/\ nCrashed = 0                       (* Initially, there is no crashed process
																					 or all processes are correct. *)
	/\ Corr = Proc
	/\ sent = {}                          (* No messages are sent. *)
	/\ pc \in [ Proc -> {"V0", "V1"} ]    (* If process p received an INIT message,
																					 process p is initialized with V1. Otherwise,
																					 it is initialized with V0. *)
	/\ rcvd = [ i \in Proc |-> {} ]       (* No messages are received. *)


InitNoBcast ==
	/\ nCrashed = 0                       (* Initially, there is no crashed process
																					 or all processes are correct. *)
	/\ Corr = Proc
	/\ sent = {}                          (* No messages are sent. *)
	/\ pc = [ p \in Proc |-> "V0" ]       (* Nothing is broadcasted and
																					 no process receives an INIT message. *)
	/\ rcvd = [ i \in Proc |-> {} ]       (* No messages are received. *)

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
	/\   \/ UponV1(self)
		 \/ UponAccept(self)
		 \/ UponCrash(self)
		 \/ UNCHANGED << pc, sent, nCrashed, Corr >>

(* the transition step *)
Next ==  (\E self \in Corr: Step(self))

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

(* If no correct process does not broadcast then no correct processes accepts. *)
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] /= "AC")

(* Unforg is correct iff the initial state is InitNoBcast. *)
Unforg == (\A self \in Corr: (pc[self] /= "AC"))

(* If a correct process broadcasts, then every correct process eventually accepts. *)
CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\E i \in Corr: pc[i] = "AC")

(* If a correct process accepts, then every correct process eventually accepts.  *)
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))


(* If a message is sent by a correct process, then every correct processes eventually
	 receives this message. *)
ReliableChan ==
	[]( \E sndr \in {x \in Nat: 1 <= x /\ x <= N} : (<<sndr, "ECHO">> \in sent
														=> <>[](\A p \in Corr : <<sndr, "ECHO">> \in rcvd[p])))

\* @type: (Seq(STATE), Int) => Bool;
UnforgTrace(hist, loopStartIndex) ==
  LET firstState == hist[1] IN
  (\A i \in firstState.Corr: firstState.pc[i] = "V0") =>
    \A step \in DOMAIN hist:
      LET state == hist[step] IN
        (\A i \in state.Corr: state.pc[i] /= "AC")

\* @type: (Seq(STATE), Int) => Bool;
CorrTrace(hist, loopStartIndex) ==
  LET firstState == hist[1] IN
    (\A i \in firstState.Corr: firstState.pc[i] = "V1") =>
      /\ (\E index \in DOMAIN hist: 
            LET state == hist[index] IN
              \E i \in state.Corr: state.pc[i] = "AC")

\* \* @type: (Seq(STATE), Int) => Bool;
\* RelayTrace(hist) ==
\* 	LET LoopStartIndex == CHOOSE x \in DOMAIN hist: hist[x].LoopSelector IN
\* 	LET range(a,b) == {x \in DOMAIN hist: a <= x /\ x <= b } IN
\* 	LoopExists /\ LoopOK(hist) =>
\* 		\A step \in DOMAIN hist:
\* 			LET curState == hist[step] IN
\* 			(\E i \in curState.Corr: curState.pc[i] = "AC")
\* 				=> \E otherStep \in range((IF step < LoopStartIndex \/ ~LoopExists THEN step ELSE LoopStartIndex), Len(hist)):
\* 					LET otherState == hist[otherStep] IN
\* 							\A i \in otherState.Corr: otherState.pc[i] = "AC"

\* \* @type: (Seq(STATE), Int) => Bool;
\* ReliableTrace(hist) ==
\*     LET LoopStartIndex == CHOOSE x \in DOMAIN hist: hist[x].LoopSelector IN
\*     LET range(a,b) == {x \in DOMAIN hist: a <= x /\ x <= b } IN
\*         LoopExists /\ LoopOK(hist) =>
\*             \A step \in DOMAIN hist: LET curState == hist[step] IN \E sndr \in 1..N : (<<sndr, "ECHO">> \in curState.sent
\*                 => (\E step2 \in range((IF step < LoopStartIndex \/ ~LoopExists THEN step ELSE LoopStartIndex), Len(hist)):
\*                     \A step3 \in range((IF step2 < LoopStartIndex \/ ~LoopExists THEN step2 ELSE LoopStartIndex), Len(hist)):
\*                         \A p \in hist[step3].Corr : <<sndr, "ECHO">> \in hist[step3].rcvd[p]))

\* @type: (Seq(STATE), Int) => Bool;
LoopOk(hist, loopIndex) ==
	LET lastState == hist[Len(hist)] IN
  LET loopState == hist[loopIndex] IN
  /\ loopState.Corr = lastState.Corr
  /\ loopState.nCrashed = lastState.nCrashed
  /\ loopState.pc = lastState.pc
  /\ loopState.rcvd = lastState.rcvd
  /\ loopState.sent = lastState.sent

\* @type: (Seq(STATE), Int, Int) => Bool;
ReceiveEnabled(hist, index, nextIndex) ==
  LET state == hist[index] IN
  \E p \in state.Corr: \E msg \in state.sent: msg \notin state.rcvd[p]

\* @type: (Seq(STATE), Int, Int) => Bool;
V1Enabled(hist, index, nextIndex) ==
  LET state == hist[index] IN
  \E p \in state.Corr: state.pc[p] = "V1"

\* @type: (Seq(STATE), Int, Int) => Bool;
AcceptEnabled(hist, index, nextIndex) ==
  LET state == hist[index] IN
  LET nextState == hist[nextIndex] IN
  \E p \in state.Corr:
    /\ (state.pc[p] = "V0" \/ state.pc[p] = "V1")     
    /\ nextState.rcvd[p] # {}

\* @type: (Seq(STATE), Int) => Bool;
LoopFair(hist, loopStartIndex) ==
  LET loopState == hist[loopStartIndex] IN
  \A index \in {x \in DOMAIN hist: x >= loopStartIndex}:
    LET nextIndex == IF index = Len(hist) THEN loopStartIndex ELSE index+1 IN
    /\ ~ReceiveEnabled(hist, index, nextIndex)
    /\ ~V1Enabled(hist, index, nextIndex)
    /\ ~AcceptEnabled(hist, index, nextIndex) 

\* @type: Seq(STATE) => Bool;
Property(hist) ==
    \A loopIndex \in DOMAIN hist: (LoopOk(hist, loopIndex) /\ LoopFair(hist, loopIndex) => CorrTrace(hist, loopIndex))


=============================================================================
\* Modification History
\* Last modified Mon Sep 03 17:01:26 CEST 2018 by tthai
