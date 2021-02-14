package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{FixedArity, OperArity}

/**
 * Convenient shortcuts and definitions. Import them, when needed.
 */
package object convenience {

  /**
   * This is just a short-hand to Builder, so one can type more naturally, e.g., tla.plus(tla.int(2), tla.int(3))
   */
  val tla: Builder.type = Builder

  implicit def makeUID(id: Int): UID = UID(id)

  implicit def opArity(n: Int): OperArity = FixedArity(n)
}
