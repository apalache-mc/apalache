package at.forsyte.apalache.tla.obsolete.ir

/**
 * Every object of TLA intermediate representation inherits from this one.
 * Case classes implement different types of TLA nodes.
 * Note that using this hierarchy allows badly-formed expressions,
 * i.e., one can define weird expressions like a variable with two formal parameters.
 * We will probably add consistency checks later.
 */
sealed abstract class TlaNode
/**
 * A declaration of a user-defined operator, e.g., of a variable.
 * UserOpDecl differs from UserOpDef in that the former does not have a body.
 */
case class UserOpDecl(kind: Kind.Value, uniqueName: String, arity: Int, origin: Origin)
  extends TlaNode
/** A user-defined operator */
case class UserOpDef(uniqueName: String, params: List[FormalParam], body: TlaNode, origin: Origin)
  extends TlaNode
/** A built-in operator */
case class BuiltinOp(uniqueName: String, params: List[FormalParam], origin: Origin)
  extends TlaNode
/**
 * A formal parameter
 *
 * @param arity the arity of the parameter, i.e., the parameter is an operator
 * @param isLeibniz when true, then the parameter is Leibniz,
 *                  i.e., it respects substitution: A = B => F(A) = F(B).
 *
 * @see L. Lamport. TLA+2: a preliminary guide, p. 7. 15 Jan 2014.
 */
case class FormalParam(uniqueName: String, arity: Int, isLeibniz: Boolean = true)
  extends TlaNode
/** Operator application */
case class OpApply(oper: TlaNode, args: List[TlaNode], origin: Origin)
  extends TlaNode
/** An assumption */
case class Assumption(body: UserOpDef, origin: Origin)
  extends TlaNode
/** An axiom */
case class Axiom(body: UserOpDef, origin: Origin)
  extends TlaNode
/** A theorem */
case class Theorem(body: UserOpDef, origin: Origin)
  extends TlaNode