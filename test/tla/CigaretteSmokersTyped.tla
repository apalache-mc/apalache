---------------------- MODULE CigaretteSmokersTyped --------------------------
(***************************************************************************)   
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(*                                                                         *)
(* This specification has been extended with type annotations for the      *)
(* demonstration purposes. Some parts of the original specification are    *)
(* omitted for brevity.                                                    *)
(*                                                                         *)
(* The original specification by @mryndzionek can be found here:           *)
(* https://github.com/tlaplus/Examples/blob/master/specifications/CigaretteSmokers/CigaretteSmokers.tla *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Typing

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(* try to guess the types in the code below *)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(* type assumptions for the type checker *)
TypeAssumptions ==
    /\ AssumeType(Ingredients, "Set(INGREDIENT)")
    /\ AssumeType(Offers, "Set(Set(INGREDIENT))")
    /\ AssumeType(smokers, "INGREDIENT -> [smoking: Bool]")
    /\ AssumeType(dealer, "Set(INGREDIENT)")

vars == <<smokers, dealer>>       

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

(* this operator has a parametric signature *)
ChooseOne(S, P(_)) ==
    "(Set(INGREDIENT), (INGREDIENT) => Bool) => INGREDIENT" ##
    (CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x)

Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

startSmoking ==
    /\ dealer /= {}
    /\ smokers' = [r \in Ingredients |->
                    [smoking |-> {r} \cup dealer = Ingredients]]
    /\ dealer' = {}

stopSmoking ==
    /\ dealer = {}
        (* the type of LAMBDA should be inferred from the types
           of ChooseOne and Ingredients *)
    /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
       IN smokers' = [smokers EXCEPT ![r].smoking = FALSE] 
    /\ dealer' \in Offers

Next ==
    startSmoking \/ stopSmoking

Spec ==
    Init /\ [][Next]_vars

FairSpec ==
    Spec /\ WF_vars(Next)    

AtMostOne ==
    Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
=============================================================================
