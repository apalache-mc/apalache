----------------------------- MODULE BlockchainP1 -----------------------------
(* 
   This is simplification of ../../spec/light-client/Blockchain.tla that uses
   the following assumptions:
   
   - The validators can only have voting power of 1.
   - As a result, we are using sets and cardinalities instead of functions
     (effectively, multi-sets) and recursive operators.
     
   ----------------------------------------------------------------------------  

   This is a high-level specification of Tendermint blockchain
   that is designed specifically for:
   
   (1) Lite client, and
   (2) Fork accountability.
 *)
EXTENDS Integers, Sequences, FiniteSets

(* APALACHE *)
a <: b == a

NT == STRING \* the type of nodes (it could be Int as well)
(* END OF APALACHE *)

Min(a, b) == IF a < b THEN a ELSE b

CONSTANT
  AllNodes,
    (* a set of all nodes that can act as validators (correct and faulty) *)
  ULTIMATE_HEIGHT
    (* a maximal height that can be ever reached (modelling artifact) *)

Heights == 0..ULTIMATE_HEIGHT   (* possible heights *)

(* A commit is just a set of nodes who have committed the block *)
Commits == SUBSET AllNodes

(* The set of all block headers that can be on the blockchain.
   This is a simplified version of the Block data structure in the actual implementation. *)
BlockHeaders == [
  height: Heights,
    \* the block height
  lastCommit: Commits,
    \* the nodes who have voted on the previous block, the set itself instead of a hash
  (* in the implementation, only the hashes of V and NextV are stored in a block,
     as V and NextV are stored in the application state *) 
  VS: SUBSET AllNodes(* \ {{} <: {NT}}*),
    \* the validators of this block together with their voting powers,
    \* i.e., a multi-set. We store the validators instead of the hash.
  NextVS: SUBSET AllNodes(* \ {{} <: {NT}}*)
    \* the validators of the next block together with their voting powers,
    \* i.e., a multi-set. We store the next validators instead of the hash.
]

\* a hint for apalache about the type of an element of BlockHeaders
BHT == [height |-> Int, lastCommit |-> {NT}, VS |-> {NT}, NextVS |-> {NT}]

(* A convenience operator that retrieves the validator set from a header *)
VS(header) == header.VS

(* A convenience operator that retrieves the next validator set from a header *)
NextVS(header) == header.NextVS

(* A signed header is just a header together with a set of commits *)
\* TODO: Commits is the set of PRECOMMIT messages
SignedHeaders == [header: BlockHeaders, Commits: Commits]

\* a hint for apalache about the type of an element of SignedHeaders
SHT == [header |-> BHT, Commits |-> {NT}]

VARIABLES
    tooManyFaults,
    (* whether there are more faults in the system than the blockchain can handle *)
    height,
    (* the height of the blockchain, starting with 0 *)
    minTrustedHeight,
    (* The global height of the oldest block that is younger than
       the trusted period (AKA the almost rotten block).
       In the implementation, this is the oldest block,
       where block.bftTime + trustingPeriod >= globalClock.now. *)
    blockchain,
    (* A sequence of BlockHeaders, which gives us a bird view of the blockchain. *)
    Faulty
    (* A set of faulty nodes, which can act as validators. We assume that the set
       of faulty processes is non-decreasing. If a process has recovered, it should
       connect using a different id. *)
       
(* all variables, to be used with UNCHANGED *)       
vars == <<tooManyFaults, height, minTrustedHeight, blockchain, Faulty>>         

(* The set of all correct nodes in a state *)
Corr == AllNodes \ Faulty       

(****************************** BLOCKCHAIN ************************************)
(* in the future, we may extract it in a module on its own *)

(*
  Compute the total voting power of a subset of pNodes \subseteq AllNodes,
  restricted to a validator set. In BlockchainP1, this is fairly trivial.
*)  
PowerOfSet(pValidators, pNodes) ==
    Cardinality(pValidators \intersect pNodes)

(*
 Given a set of validators pValidators \subseteq AllNodes
 and pNodes \subseteq pValidators, test whether the set pNodes \subseteq AllNodes has
 more than 2/3 of voting power among the nodes in D.
 *)
TwoThirds(pValidators, pNodes) ==
    LET TP == Cardinality(pValidators)
        SP == PowerOfSet(pValidators, pNodes)
    IN
    3 * SP > 2 * TP \* when thinking in real numbers, not integers: SP > 2.0 / 3.0 * TP 

(*
 Given a set of validators pValidators \subseteq AllNodes
 and a set of pFaultyNodes, test whether the voting power of the correct
 nodes in pNodes is more than 2/3 of the voting power of the faulty nodes
 among the nodes in pNodes.
 *)
IsCorrectPowerForSet(pFaultyNodes, pValidators, pNodes) ==
    LET FN == pFaultyNodes \intersect pNodes  \* faulty nodes in pNodes
        CN == pNodes \ pFaultyNodes           \* correct nodes in pNodes
        CP == PowerOfSet(pValidators, CN)   \* power of the correct nodes
        FP == PowerOfSet(pValidators, FN)   \* power of the faulty nodes
    IN
    \* CP + FP = TP is the total voting power, so we write CP > 2.0 / 3 * TP as follows:
    CP > 2 * FP \* Note: when FP = 0, this implies CP > 0.

(*
 Given a set of validators pValidators \subseteq AllNodes
 and a set of pFaultyNodes, test whether the voting power of the correct nodes in D
 is more than 2/3 of the voting power of the faulty nodes in D.
 *)
IsCorrectPower(pFaultyNodes, pValidators) ==
    IsCorrectPowerForSet(pFaultyNodes, pValidators, pValidators)
    
(* This is what we believe is the assumption about failures in Tendermint *)     
FaultAssumption(pFaultyNodes, pMinTrustedHeight, pBlockchain) ==
    \A h \in 1..ULTIMATE_HEIGHT:
        (pMinTrustedHeight <= h /\ h <= Len(pBlockchain))
            => IsCorrectPower(pFaultyNodes, pBlockchain[h].NextVS)


(* A signed header whose commit coincides with the last commit of a block,
   unless the commits are made by the faulty nodes *)
SoundSignedHeaders(ht) ==
    { sh \in SignedHeaders:
        \/ sh.header = blockchain[ht] \* signed by correct and faulty (maybe)
        \/ sh.Commits \subseteq Faulty /\ sh.header.height = ht \* signed only by faulty
    }


(* Append a new block on the blockchain.
   Importantly, more than 2/3 of voting power in the next set of validators
   belongs to the correct processes. *)       
AppendBlock ==
  LET last == blockchain[Len(blockchain)] IN
  \E lastCommit \in SUBSET (VS(last)) \ {{} <: {NT} },
     NextV \in SUBSET AllNodes \ {{} <: {NT}}:
    LET new == [ height |-> height + 1, lastCommit |-> lastCommit,
                 VS |-> last.NextVS, NextVS |-> NextV ] IN
    /\ TwoThirds(last.VS, lastCommit)
    /\ IsCorrectPower(Faulty, NextV) \* the correct validators have >2/3 of power
    /\ blockchain' = Append(blockchain, new)
    /\ height' = height + 1

(* Initialize the blockchain *)
Init ==
  /\ height = 1             \* there is just genesis block
  /\ minTrustedHeight = 1   \* the genesis is initially trusted
  /\ Faulty = {} <: {NT}           \* initially, there are no faults
  /\ tooManyFaults = FALSE  \* there are no faults
  (* pick a genesis block of all nodes where next correct validators have >2/3 of power *)
  /\ \E NextV \in SUBSET AllNodes:          \* pick a next validator set
         LET \* assume that the genesis contains all the nodes
             \* and construct the genesis block
             genesis == [ height |-> 1, lastCommit |-> {} <: {NT},
                          VS |-> AllNodes, NextVS |-> NextV]
         IN
         /\ NextV /= {} <: {NT}    \* assume that there is at least one next validator 
         /\ blockchain = <<genesis>> <: Seq(BHT) \* initially, blockchain contains only the genesis

(********************* BLOCKCHAIN ACTIONS ********************************)
          
(*
  The blockchain may progress by adding one more block, provided that:
     (1) The ultimate height has not been reached yet, and
     (2) The faults are within the bounds.
 *)
AdvanceChain ==
  /\ height < ULTIMATE_HEIGHT /\ ~tooManyFaults
  /\ AppendBlock
  /\ UNCHANGED <<minTrustedHeight, tooManyFaults, Faulty>>

(*
  As time is passing, the minimal trusted height may increase.
  As a result, the blockchain may move out of the faulty zone.
  *)
AdvanceTime ==
    \* a modification for apalache
  /\ minTrustedHeight' \in
    {h \in Heights:
     h > minTrustedHeight /\ h <= height + 1 /\ h <= ULTIMATE_HEIGHT }
  /\ tooManyFaults' = ~FaultAssumption(Faulty, minTrustedHeight', blockchain)
  /\ UNCHANGED <<height, blockchain, Faulty>>

(* One more process fails. As a result, the blockchain may move into the faulty zone. *)
OneMoreFault ==
  /\ \E n \in AllNodes \ Faulty:
      /\ Faulty' = Faulty \cup {n}
      /\ Faulty' /= AllNodes \* at least process remains non-faulty
      /\ tooManyFaults' = ~FaultAssumption(Faulty', minTrustedHeight, blockchain)
  /\ UNCHANGED <<height, minTrustedHeight, blockchain>>

(* stuttering at the end of the blockchain *)
StutterInTheEnd == 
  height = ULTIMATE_HEIGHT /\ UNCHANGED vars

(* Let the blockchain to make progress *)
Next ==
  \/ AdvanceChain
  \/ AdvanceTime
  \/ OneMoreFault
  \/ StutterInTheEnd

(********************* PROPERTIES TO CHECK ********************************)

(* Invariant: it should be always possible to add one more block unless:
  (1) either there are too many faults,
  (2) or the bonding period of the last transaction has expired, so we are stuck.
 *)
NeverStuck ==
  \/ tooManyFaults
  \/ height = ULTIMATE_HEIGHT
  \/ minTrustedHeight > height \* the trusting period has expired
  \/ ENABLED AdvanceChain

(* The next validator set is never empty *)
NextVSNonEmpty ==
    \A h \in 1..ULTIMATE_HEIGHT:
      (h <= Len(blockchain)) => NextVS(blockchain[h]) /= ({} <: {NT})

(* False properties that can be checked with TLC, to see interesting behaviors *)

(* Check this to see how the blockchain can jump into the faulty zone *)
NeverFaulty == ~tooManyFaults

(* False: it should be always possible to add one more block *)
NeverStuckFalse1 ==
  ENABLED AdvanceChain

(* False: it should be always possible to add one more block *)
NeverStuckFalse2 ==
  \/ tooManyFaults
  \/ height = ULTIMATE_HEIGHT
  \/ ENABLED AdvanceChain

=============================================================================
\* Modification History
\* Last modified Tue Nov 26 13:23:21 CET 2019 by igor
\* Created Fri Oct 11 15:45:11 CEST 2019 by igor
