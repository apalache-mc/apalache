package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.UID

/**
  * A reference to the source expression. Some expressions have the exact source, so their type coincides with
  * the type of the source expression. For those expressions, we use ExactRef.
  * Other expressions are auxillary expressions, so they only point to the source
  * expression, in order to understand type errors, but they should not be used to collect types.
  * For those expressions, we use BlameRef.
  *
  * @author Igor Konnov
  */
sealed trait EtcRef {
  def tlaId: UID
}

/**
  * An exact reference to the source TLA+ expression. Once the type of an expression with ExactRef has been found,
  * we can draw conclusions about the types of the source TLA+ expression.
  *
  * @param tlaId the id of the original TLA+ expression
  */
case class ExactRef(tlaId: UID) extends EtcRef {
  override def toString: String = "E" + tlaId
}

/**
  * A blame reference to the source TLA+ expression. This reference should be used to report type errors,
  * but it should not be used for drawing conclusions about the type of the original expression.
  *
  * @param tlaId the id of the original TLA+ expression
  */
case class BlameRef(tlaId: UID) extends EtcRef {
  override def toString: String = "B" + tlaId
}
