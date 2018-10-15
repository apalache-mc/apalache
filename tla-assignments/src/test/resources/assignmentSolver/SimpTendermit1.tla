--------------------------- MODULE SimpTendermit1 ---------------------------
(*
 A TLA+ specification of Simplified Tendermint in the synchronous model with symmetric
 Byzantine faults (Algorithm 1).
 
 Based on the pseudo-code from the arxiv publication 1809.09858v1 [cs.DC] 26 Sep 2018.
 
 Encoded in TLA+ by Igor Konnov
 *)
 
EXTENDS Integers 
 
N == 4 \* the total number of processes: correct and faulty
F == 1 \* the number of Byzantine processes (symmetric faults)
Heights == 0..1 \* the set of consensus instances
Epochs == 0..2  \* the set of epochs
Procs == 1..(N - F)
Faulty == (N - F + 1)..N
ValidValues == 0..1     \* e.g., picked by a correct process, or a faulty one
InvalidValues == 2..2   \* e.g., sent by a Byzantine process
nil == -1

\* these variables are exactly as in the pseudo-code
VARIABLES h, e, decision, proposal, vote

\* book-keeping variables
VARIABLES round, faultyMessages

Init == /\ h = [p \in Procs |-> 0]
        /\ e = [p \in Procs |-> 0]
        /\ decision = [p \in Procs |-> [ht \in Heights |-> nil]]
        /\ proposal \in [Procs -> ValidValues]
        /\ vote = [p \in Procs |-> nil]
        \* book-keeping
        /\ round = "PRE-PROPOSE"
        /\ faultyMessages = {}

\* "a deterministic function which gives the proposer
\*  for a given epoch at a given height in a round robin fashion"
Proposer(p) == 1 + ((h[p] + e[p]) % N)

IsValid(v) == v \in ValidValues

Id(v) == v

SentCorrect(p) ==
    CASE   round = "PRE-PROPOSE" ->
            IF Proposer(p) = p
            THEN { [type |-> "PRE-PROPOSE", src |-> p, height |-> h[p], epoch |-> e[p], proposal |-> proposal[p]] }
            ELSE {}
        [] round = "PROPOSE" ->
            { [type |-> "PROPOSE", height |-> h[p], epoch |-> e[p], proposal |-> proposal[p]] }
        [] round = "VOTE" ->
            { [type |-> "VOTE", height |-> h[p], epoch |-> e[p], vote |-> vote[p]] }
            
PreProposeFaulty ==
    SUBSET [type: {"PRE-PROPOSE"}, src: Faulty, height: Heights,
             epoch: Epochs, proposal: ValidValues \cup InvalidValues]

ProposeFaulty ==
    SUBSET [type: {"PROPOSE"}, src: Faulty, height: Heights,
             epoch: Epochs, proposal: ValidValues \cup InvalidValues]

VoteFaulty ==
    SUBSET [type: {"VOTE"}, height: Heights,
             epoch: Epochs, vote: ValidValues \cup InvalidValues]
            
IsSentByFaulty ==
    faultyMessages' \in
        CASE   round = "PRE-PROPOSE" -> PreProposeFaulty
            [] round = "PROPOSE" -> ProposeFaulty
            [] round = "VOTE" -> VoteFaulty
           

Deliver(p, sent) ==
    CASE    round = "PRE-PROPOSE" ->
            { m \in sent : m.type = "PRE-PROPOSE" /\ m.src = Proposer(p) /\ m.height = h[p] /\ m.epoch = e[p] }
            
        [] round = "PROPOSE" ->
            { m \in sent : m.type = "PROPOSE" /\ m.height = h[p] /\ m.epoch = e[p] }
            
        [] round = "VOTE" ->
            { m \in sent : m.type = "VOTE" /\ m.height = h[p] /\ m.epoch = e[p] }

FindProposal(p, delivered) ==
    LET vs == { m2.proposal: m2 \in { m \in delivered[p] : m.type = "PRE-PROPOSE" /\ m.height = h[p] /\ m.epoch = h[p] /\ IsValid(m.proposal) }} IN
    IF vs = {}
    THEN nil
    ELSE CHOOSE v \in vs: TRUE \* actually, vs is a singleton set, but we use choose to pick an element

PrePropose(delivered) ==
    /\ round = "PRE-PROPOSE" /\ round' = "PROPOSE"
    /\ proposal' = [p \in Procs |-> Id(FindProposal(p, delivered))]
    /\ UNCHANGED <<vote, h, e, decision>>

ChooseValue(p, delivered) ==
    LET vs == { m2.proposal: m2 \in { m \in delivered[p] : m.type = "PROPOSE" /\ m.height = h[p] /\ m.epoch = h[p] }} IN
    IF vs = {}
    THEN nil
    ELSE LET chosen == CHOOSE v \in vs: TRUE IN
        IF IsValid(chosen) THEN chosen ELSE nil

        
Propose(delivered) ==
    /\ round = "PROPOSE" /\ round' = "VOTE"
    /\ vote' = [p \in Procs |-> Id(ChooseValue(p, delivered))]
    /\ UNCHANGED <<proposal, h, e, decision>>

ChooseDecision(p, delivered) ==
    LET vs == { m2.vote: m2 \in { m \in delivered[p] : m.type = "VOTE" /\ m.height = h[p] /\ m.epoch = h[p] }} IN
    IF vs = {}
    THEN nil
    ELSE LET decided == CHOOSE v \in vs: TRUE IN
        IF IsValid(decided) THEN decided ELSE nil
        
IsDecidedNow(p, d) == d[p] /= nil /\ decision[p][h[p]] = nil

Overflow(p) == h[p] \notin Heights \/ e[p] \notin Epochs
        
Vote(delivered) ==
    /\ round = "VOTE" /\ round' = "PRE-PROPOSE"
    /\ LET d == [ p \in Procs |-> ChooseDecision(p, delivered)] IN
        /\ decision' = [ p \in Procs |->
            IF Overflow(p)
            THEN decision[p]
            ELSE [decision[p] EXCEPT ![h[p]] =   
                    IF IsDecidedNow(p, d) THEN d[p] ELSE decision[p][h[p]]
                 ]]
        /\ h' = [ p \in Procs |->
            IF ~Overflow(p) /\ IsDecidedNow(p, d) THEN h[p] + 1 ELSE h[p] ]
        /\ e' = [ p \in Procs |->
            IF Overflow(p) \/ IsDecidedNow(p, d) THEN e[p] ELSE e[p] + 1 ]
        /\ proposal' \in [Procs -> ValidValues \cup InvalidValues \cup {nil}]
        (* since we have to non-deterministically chose a value, this seems to be the only way *)
        /\ \A p \in Procs:
            IF Overflow(p) \/ IsDecidedNow(p, d)
            THEN proposal'[p] = proposal[p]
            ELSE proposal'[p] \in ValidValues
    /\ UNCHANGED <<vote>>


Compute(delivered) ==
    PrePropose(delivered) \/ Propose(delivered) \/ Vote(delivered)
        
Next ==
    /\ IsSentByFaulty
    /\ LET sent == faultyMessages' \cup (UNION { SentCorrect(p) : p \in Procs }) IN
       LET delivered == [ p \in Procs |-> Deliver(p, sent) ] IN
       Compute(delivered)
       (*
    /\ IsSentByFaulty
    /\ Compute([ p \in Procs |-> Deliver(p, faultyMessages' \cup (UNION { SentCorrect(q) : q \in Procs })) ])
        *)

NextNoFaults ==
    /\ UNCHANGED faultyMessages
    /\ LET sent == UNION { SentCorrect(p) : p \in Procs } IN
       LET delivered == [ p \in Procs |-> Deliver(p, sent) ] IN
       Compute(delivered)


Agreement ==
    \A ht \in Heights: \A p, q \in Procs:
        decision[p][ht] = nil \/ decision[q][ht] = nil \/ decision[p][ht] = decision[q][ht]  

=============================================================================
\* Modification History
\* Last modified Sat Oct 13 20:24:28 CEST 2018 by igor
\* Created Fri Oct 05 14:32:58 CEST 2018 by igor
