package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{NameEx, ValEx}

/**
  * Implements the rule SE-INT-CONST.
  *
  * @author Igor Konnov
  */
class IntConstRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaInt(_)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaInt(n)) =>
        if (!n.isValidInt) {
          throw new RewriterException("BigInt %s does not fit into integer range. Do not know how to translate in SMT"
            .format(n))
        }
        val intConst = rewriter.intValueCache.getOrCreate(n.toInt)
        val finalState =
          state.setTheory(IntTheory()).setRex(NameEx(intConst))
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
