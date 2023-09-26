package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaType1, Typed, Untyped}
import at.forsyte.apalache.tla.types.tla

/**
 * Rename x' to NameEx("x'"). We only consider the case when prime is applied to a variable.
 *
 * @author
 *   Igor Konnov
 */
class PrimeRule extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaActionOper.prime, _) => true
      case _                              => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaActionOper.prime, nEx @ NameEx(name)) =>
        nEx.typeTag match {
          case Typed(tt1: TlaType1) => state.setRex(tla.name(name + "'", tt1))
          case _                    => throw new InternalCheckerError("Internal expressions should be Typed", nEx)
        }

      case _ =>
        throw new RewriterException("Prime operator is only implemented for variables", state.ex)
    }
  }
}
