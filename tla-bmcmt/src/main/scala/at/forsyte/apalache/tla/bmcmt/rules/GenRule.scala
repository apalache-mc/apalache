package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.ValueGenerator
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{OperEx, TlaType1, ValEx}

/**
 * Implements a rule for Apalache!Gen.
 *
 * @author Igor Konnov
 */
class GenRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(ApalacheOper.gen, _) => true
      case _                           => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(ApalacheOper.gen, ValEx(TlaInt(bound))) if bound.isValidInt && bound.toInt > 0 =>
        val resultType = TlaType1.fromTypeTag(state.ex.typeTag)
        new ValueGenerator(rewriter, bound.toInt).gen(state, resultType)

      case ex @ OperEx(ApalacheOper.gen, boundEx) =>
        throw new RewriterException("Apalache!Gen expects a constant positive integer. Found: " + boundEx, ex)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
