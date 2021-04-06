--------------------------- MODULE Apalache -----------------------------------
(*****************************************************************************)
(* This is a standard module for use with the Apalache model checker.        *)
(* The meaning of the operators is explained in the comments.                *)
(* Many of the operators serve as additional annotations of their arguments. *)
(* As we like to preserve compatibility with TLC and TLAPS, we define the    *)
(* operator bodies by erasure. The actual interpretation of the operators is *)
(* encoded inside Apalache. For the moment, these operators are mirrored in  *)
(* the class at.forsyte.apalache.tla.lir.oper.BmcOper.                       *)
(*                                                                           *)
(* Igor Konnov, 2020                                                         *)
(*****************************************************************************)

(*****************************************************************************)
(* An assignment of an expression e to a state variable x. Typically, one    *)
(* uses the non-primed version of x in the initializing predicate Init and   *)
(* the primed version of x (that is, x') in the transition predicate Next.   *)
(* Although TLA+ does not have a concept of a variable assignment, we find   *)
(* this concept extremely useful for symbolic model checking. In pure TLA+,  *)
(* one would simply write x = e, or x \in {e}.                               *)
(*                                                                           *)
(* Apalache automatically converts some expressions of the form              *)
(* x = e or x \in {e} into assignments. However, if you like to annotate     *)
(* assignments by hand, you can use this operator.                           *)
(*                                                                           *)
(* For a further discussion on that matter, see:                             *)
(* https://github.com/informalsystems/apalache/blob/ik/idiomatic-tla/docs/idiomatic/assignments.md *)
(*****************************************************************************)
x := e == x = e

(*****************************************************************************)
(* A generator of a data structure. Given a positive integer `bound`, and    *)
(* assuming that the type of the operator application is known, we           *)
(* recursively generate a TLA+ data structure as a tree, whose width is      *)
(* bound by the number `bound`.                                              *)
(*                                                                           *)
(* The body of this operator is redefined by Apalache.                       *)
(*****************************************************************************)
Gen(size) == {}

(*****************************************************************************)
(* As TLA+ is untyped, one can use function- and sequence-specific operators *)
(* interchangeably. However, to maintain correctness w.r.t. our type-system, *)
(* an explicit cast is needed when using functions as sequences.             *)
(*****************************************************************************)
LOCAL INSTANCE Sequences
FunAsSeq(fn, maxSeqLen) == SubSeq(fn, 1, maxSeqLen)

(*****************************************************************************)
(* Annotating an expression \E x \in S: P as Skolemizable. That is, it can   *)
(* be replaced with an expression c \in S /\ P(c) for a fresh constant c.    *)
(* Not every exisential can be replaced with a constant, this should be done *)
(* with care. Apalache detects Skolemizable expressions by static analysis.  *)
(*****************************************************************************)
Skolem(e) == e

(*****************************************************************************)
(* A hint to the model checker to expand a set S, instead of dealing         *)
(* with it symbolically. Apalache finds out which sets have to be expanded   *)
(* by static analysis.                                                       *)
(*****************************************************************************)
Expand(S) == S

(*****************************************************************************)
(* A hint to the model checker to replace its argument Cardinality(S) >= k   *)
(* with a series of existential quantifiers for a constant k.                *)
(* Similar to Skolem, this has to be done carefully. Apalache automatically  *)
(* places this hint by static analysis.                                      *)
(*****************************************************************************)
ConstCardinality(cardExpr) == cardExpr

(****************************************************************************)
(* Apalache internally defines the operator Distinct that requires all its  *)
(* arguments to be distinct from each other. We do not know how to write    *)
(* such an operator in a TLA+ module.                                       *)
(****************************************************************************)
(*
Distinct(e1, ..., ek) == ...
*)

===============================================================================
