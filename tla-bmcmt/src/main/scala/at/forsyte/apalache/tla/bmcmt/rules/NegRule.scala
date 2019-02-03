package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * Implements the rules: SE-BOOL-NEG[1-9]. The code is a bit complex, as we are trying to apply simplifications first.
  *
  * @author Igor Konnov
  */
class NegRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val substRule = new SubstRule(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.not, _) => true
      case _ => false
    }
  }

  // TODO: All the simplifications should be moved in the special preprocessing phase
  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.not, subEx@NameEx(name)) =>
        if (substRule.isApplicable(state.setRex(subEx))) {
          // e.g., y should be substituted by a Boolean value
          val newState = substRule.apply(state.setRex(subEx))
          apply(newState.setRex(OperEx(TlaBoolOper.not, newState.ex)))
        } else {
          // SE-BOOL-NEG9
          if (state.theory == CellTheory()
            && name == state.arena.cellFalse().toString) {
            state.setRex(state.arena.cellTrue().toNameEx)
          } else if (state.theory == CellTheory()
            && name == state.arena.cellTrue().toString) {
            state.setRex(state.arena.cellFalse().toNameEx)
          } else {
            val pred = NameEx(rewriter.solverContext.introBoolConst())
            val iff =
              if (BoolTheory().hasConst(name) || CellTheory().hasConst(name)) {
                // pred <=> !b
                OperEx(TlaBoolOper.equiv, pred, OperEx(TlaBoolOper.not, subEx))
              } else {
                throw new RewriterException("Unexpected theory in NegRule: " + state.theory)
              }

            rewriter.solverContext.assertGroundExpr(iff)
            val finalState = state.setRex(pred).setTheory(BoolTheory())
            // coerce back, if needed
            rewriter.coerce(finalState, state.theory)
          }
        }

      case OperEx(TlaBoolOper.not, ex: TlaEx) =>
        // SE-BOOL-NEG[1-8]
        val rewritten = rewriteNot(ex)
        if (rewritten.isDefined)
          state.setRex(rewritten.get)
        else {
          // the general case, when no rewriting rule applies
          val newState = rewriter.rewriteUntilDone(state.setRex(ex).setTheory(BoolTheory()))
          val pred = rewriter.solverContext.introBoolConst()
          rewriter.solverContext.assertGroundExpr(tla.eql(tla.not(tla.name(pred)), newState.ex))
          val finalState = newState.setRex(tla.name(pred))
          // coerce back, if needed
          rewriter.coerce(finalState, state.theory)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def rewriteNot(root: TlaEx) = {
    root match {
      case OperEx(TlaBoolOper.or, es@_*) => // SE-BOOL-NEG1
        Some(tla.and(es map tla.not :_*))

      case OperEx(TlaBoolOper.and, es@_*) => // SE-BOOL-NEG2
        Some(tla.or(es map tla.not :_*))

      case OperEx(TlaBoolOper.implies, lhs, rhs) => // SE-BOOL-NEG3
        Some(tla.and(lhs, tla.not(rhs)))

      case OperEx(TlaBoolOper.equiv, lhs, rhs) => // SE-BOOL-NEG4
        Some(tla.equiv(tla.not(lhs), rhs))

      case OperEx(TlaBoolOper.not, e) =>  // SE-BOOL-NEG5
        Some(e)

      case OperEx(TlaBoolOper.exists, x, set, pred) => // SE-BOOL-NEG6
        Some(tla.forall(x, set, tla.not(pred)))

      case OperEx(TlaBoolOper.forall, x, set, pred) => // SE-BOOL-NEG7
        Some(tla.exists(x, set, tla.not(pred)))

      case _ =>
        None
    }
  }
}
