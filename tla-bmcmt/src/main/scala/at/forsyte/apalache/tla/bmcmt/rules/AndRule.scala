package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.values.TlaFalse
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

/**
  * Implements the rules: SE-AND[1-4].
  *
  * @author Igor Konnov
  */
class AndRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.and, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    val falseConst = state.solverCtx.falseConst
    state.ex match {
      case OperEx(TlaBoolOper.and, args@_*) =>
        // We preprocess the arguments twice: before rewriting them and after rewriting them
        // Hence, we call preprocessOrCall two times.
        def mapPreprocessMkAnd: SymbState = {
          val (newState: SymbState, preds: Seq[TlaEx]) =
            rewriter.rewriteSeqUntilDone(state.setTheory(BoolTheory()), args)

          def mkAnd: SymbState = {
            val newPred = state.solverCtx.introBoolConst()
            val cons = OperEx(TlaBoolOper.equiv,
              NameEx(newPred),
              OperEx(TlaBoolOper.and, preds: _*))
            newState.solverCtx.assertGroundExpr(cons)
            newState.setRex(NameEx(newPred))
          }

          preprocessOrCall(newState, preds, mkAnd)
        }

        val finalState = preprocessOrCall(state, args, mapPreprocessMkAnd)
        rewriter.coerce(finalState, state.theory) // coerce if needed

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def preprocessOrCall(state: SymbState, args: Seq[TlaEx],
                               defaultFun: => SymbState) = {
    // funny syntax for a function without arguments (similar to Unit-functions in OCaml)
    def isFalse(ex: TlaEx): Boolean =
      ex match {
        case ValEx(TlaFalse) =>
          true

        case NameEx(name) =>
          (name == state.arena.cellFalse().toString
            || name == state.solverCtx.falseConst)

        case _ =>
          false
      }

    if (args.isEmpty) {
      // empty conjunction is always true
      state.setTheory(BoolTheory())
        .setRex(NameEx(state.solverCtx.trueConst))

    } else if (args.exists(isFalse)) {
      // one false makes all false
      state.setTheory(BoolTheory())
        .setRex(NameEx(state.solverCtx.falseConst))
    } else {
      // note that defaultFun is called only here and thus does not add constraints in the other branches
      defaultFun
    }
  }
}
