package at.forsyte.apalache.tla.bmcmt.rules.interp

import at.forsyte.apalache.tla.typecomp.TBuilderInstruction

/**
 * @author
 *   Jure Kukovec
 */
trait ConstraintInterface {
  def addConstraint(cons: TBuilderInstruction): Unit
}
