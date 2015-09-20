package at.forsyte.apalache.tla.ir

/**
 * A statement, e.g., a theorem, an assumption, or an axiom.
 *
 * @author konnov
 */
abstract class ProofStatement
case class Assumption(body: UserOpDef) extends ProofStatement
case class Axiom(body: UserOpDef) extends ProofStatement
case class Theorem(body: UserOpDef) extends ProofStatement
