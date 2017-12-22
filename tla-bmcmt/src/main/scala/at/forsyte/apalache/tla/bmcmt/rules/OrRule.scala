package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.values.TlaTrue
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

/**
  * Implements the rules: SE-OR[1-4].
  *
  * Note that this rule does not implement case split as prescribed by rule SE-SEARCH-SPLIT.
  *
  * @author Igor Konnov
  */
class OrRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.or, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    val falseConst = state.solverCtx.falseConst
    state.ex match {
      case OperEx(TlaBoolOper.or, args@_*) =>
        // We preprocess the arguments twice: before rewriting them and after rewriting them
        // Hence, we call preprocessOrCall two times.
        def mapPreprocessMkOr: SymbState = {
          val (newState: SymbState, preds: Seq[TlaEx]) =
            rewriter.rewriteSeqUntilDone(state.setTheory(BoolTheory()), args)

          def mkOr: SymbState = {
            val newPred = state.solverCtx.introBoolConst()
            val cons = OperEx(TlaBoolOper.equiv,
              NameEx(newPred),
              OperEx(TlaBoolOper.or, preds: _*))
            newState.solverCtx.assertGroundExpr(cons)
            newState.setRex(NameEx(newPred))
          }

          preprocessOrCall(newState, preds, mkOr)
        }

        val finalState = preprocessOrCall(state, args, mapPreprocessMkOr)
        rewriter.coerce(finalState, state.theory) // coerce if needed

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def preprocessOrCall(state: SymbState, args: Seq[TlaEx],
                               defaultFun: => SymbState) = {
    // funny syntax for a function without arguments (similar to Unit-functions in OCaml)
    def isTrue(ex: TlaEx): Boolean =
      ex match {
        case ValEx(TlaTrue) =>
          true

        case NameEx(name) =>
          (name == state.arena.cellTrue().toString
            || name == state.solverCtx.trueConst)

        case _ =>
          false
      }

    if (args.isEmpty) {
      // empty disjunction is always false
      state.setTheory(BoolTheory())
        .setRex(NameEx(state.solverCtx.falseConst))

    } else if (args.exists(isTrue)) {
      // one true makes all true
      state.setTheory(BoolTheory())
        .setRex(NameEx(state.solverCtx.trueConst))
    } else {
      // note that defaultFun is called only here and thus does not add constraints in the other branches
      defaultFun
    }
  }
}
