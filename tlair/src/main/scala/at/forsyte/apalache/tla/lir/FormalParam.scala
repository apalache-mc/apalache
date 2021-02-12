package at.forsyte.apalache.tla.lir

/**
 * A formal parameter of an operator.
 */
sealed abstract class FormalParam extends Serializable {
  def name: String

  def arity: Int

}

/** An ordinary formal parameter, e.g., x used in A(x) == ... */
case class SimpleFormalParam(name: String) extends FormalParam with Serializable {
  override def arity: Int = 0
}

/** A function signature, e.g., f(_, _) used in A(f(_, _), x, y) */
case class OperFormalParam(name: String, arity: Int) extends FormalParam with Serializable {}
