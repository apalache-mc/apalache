------------------------------ MODULE bcastFolkloreTyped ------------------------------

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

EXTENDS Naturals (*, FiniteSets *)

N == 3
T == 1
F == 1

VARIABLES 
        \* @type: Set(Int);
        Corr,           (* a set of correct processes *)                          
        \* @type: Int;
        nCrashed,       (* a number of crashed processes *)
        \* @type: Int -> Str;
        pc,             (* program counters *)
        \* @type: Int -> Set(<<Int, Str>>);
        rcvd,           (* the messages received by each process *)
        \* @type: Set(<<Int, Str>>);
        sent            (* the messages sent by all correct processes *)

(*
ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
ASSUME (N > 2 * T) /\ (T >= F) /\ (F >= 0)
*)

Proc == 1 .. N                  (* all processess, including the faulty ones    *)
M == { "ECHO" }                 (* only ECHO messages are sent in this encoding *)

vars == << pc, rcvd, sent, nCrashed, Corr >>         (* a new variable Corr  *)      

Init == 
  /\ nCrashed = 0                       (* Initially, there is no crashed process  
                                           or all processes are correct. *)
  /\ Corr = 1 .. N                                           
  /\ sent = {}                          (* No messages are sent. *)
  /\ pc \in [ Proc -> {"V0", "V1"} ]    (* If process p received an INIT message,
                                           process p is initialized with V1. Otherwise,
                                           it is initialized with V0. *)
  /\ rcvd = [ i \in Proc |-> {} ]       (* No messages are received. *)        
   

Receive(self) ==                        (* a correct process self receives new messages *)
  /\ pc[self] # "CR"
  /\ 
    \/ \E msg \in sent:   (* msgs is a set of messages which has been received  *)
        rcvd' = [rcvd EXCEPT ![self] = rcvd[self] \cup {msg} ]
    \/ UNCHANGED rcvd


(* If a correct process received an INIT message or was initialized with V1, 
   it accepts this message and then broadcasts ECHO to all.  
 *)
UponV1Enabled ==
    \E i \in Proc: pc[i] = "V1"
UponV1(self) ==                                 
  /\ pc[self] = "V1"                        
  /\ pc' = [pc EXCEPT ![self] = "AC"]       
  /\ sent' = sent \cup { <<self, "ECHO">> } 
  /\ nCrashed' = nCrashed
  /\ Corr' = Corr

    

(* If a correct process received an ECHO message, it accepts and then 
   broadcasts ECHO to all.  *)
UponAcceptEnabled ==
    \E i \in Proc: pc[i] \in {"V0", "V1"} 
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

(* the transition step *)    
Next ==  (\E self \in Corr: Step(self))

(* If a correct process accepts, then every correct process eventually accepts.  *)
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))

(* if UponAccept or UponV1 is enabled, it should eventually be fired, and thus no longer be enabled. *)
Fairness ==
    ~<>[](UponV1Enabled \/ UponAcceptEnabled)

(* RelayLtl should hold when we assume fairness. *)
FairRelayLtl ==
    Fairness => RelayLtl

=============================================================================
\* Modification History
\* Last modified Wed Jun 29 15:12:30 CEST 2022 by p-offtermatt
\* Last modified Tue Sep 12 10:12:30 CEST 2017 by tthai
\* Last modified Wed Apr 05 13:19:54 CEST 2017 by tran
\* Last modified Mon Oct 03 18:32:07 CEST 2016 by tran
\* Last modified Fri Sep 09 17:20:36 CEST 2016 by TTHAI
\* Last modified Thu Sep 08 17:12:17 CEST 2016 by TTHAI
\* Last modified Fri Jan 08 16:29:40 CET 2016 by igor
\* Created Thu Mar 12 00:46:19 CET 2015 by igor
