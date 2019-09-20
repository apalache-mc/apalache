package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.analyses.FormulaHintsStore
import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

/**
  * Implement the rule for conjunction. Similar to TLC, we short-circuit A /\ B as IF A THEN B ELSE FALSE.
  * This allows us to introduce an optimization on-the-fly for the conjunctions that were marked with a hint.
  * In this optimization, we push the context, assume A and check satisfiability of the SMT context.
  * If the context is unsat, we immediately return FALSE. Otherwise, we pop the context and continue.
  *
  * @author Igor Konnov
  */
class AndRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val simplifier = new ConstSimplifier()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.and, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    val falseConst = SolverContext.falseConst
    val trueConst = SolverContext.trueConst
    simplifier.simplifyShallow(state.ex) match {
      case OperEx(TlaBoolOper.and, args@_*) =>
        val finalState =
          if (args.isEmpty) {
            // empty conjunction is always true
            state.setRex(state.arena.cellTrue().toNameEx).setTheory(CellTheory())
          } else {
            // use short-circuiting on state-level expressions (like in TLC)
            def toIte(es: Seq[TlaEx]): TlaEx = {
              es match {
                case Seq(last) => last
                case hd +: tail => tla.ite(hd, toIte(tail), NameEx(falseConst))
              }
            }

            if (!rewriter.formulaHintsStore.getHint(state.ex.ID).contains(FormulaHintsStore.HighAnd())) {
              // simply translate if-then-else to a chain of if-then-else expressions
              val newState = state.setRex(toIte(args)).setTheory(CellTheory())
              rewriter.rewriteUntilDone(newState)
            } else {
              // evaluate the conditions and prune them in runtime
              val level = rewriter.contextLevel
              rewriter.push()
              val result = shortCircuit(state, args)
              if (simplifier.isFalseConst(result.ex)) {
                rewriter.pop(rewriter.contextLevel - level) // roll back, nothing to keep
                result.setRex(state.arena.cellFalse().toNameEx).setTheory(CellTheory())
              } else {
                // We have to pop the context. Otherwise, we break the stack contract.
                rewriter.pop()
                // is there a workaround?
                val newState = state.setRex(toIte(args)).setTheory(CellTheory())
                rewriter.rewriteUntilDone(newState)
              }
            }
          }

        rewriter.coerce(finalState, state.theory) // coerce if needed

      case e@ValEx(_) =>
        // the simplifier has rewritten the disjunction to TRUE or FALSE
        rewriter.rewriteUntilDone(state.setRex(e))

      case e@_ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, e))
    }
  }

  private def shortCircuit(state: SymbState, es: Seq[TlaEx]): SymbState = {
    val cellFalse = state.arena.cellFalse()
    if (es.isEmpty) {
      state.setRex(state.arena.cellTrue().toNameEx).setTheory(CellTheory())
    } else {
      val (head, tail) = (es.head, es.tail)
      val headState = rewriter.rewriteUntilDone(state.setRex(head).setTheory(CellTheory()))
      val headCell = headState.asCell
      rewriter.solverContext.push()
      rewriter.solverContext.assertGroundExpr(headCell.toNameEx)
      val sat = rewriter.solverContext.sat()
      rewriter.solverContext.pop()
      if (!sat) {
        // always unsat, prune immediately
        headState.setRex(cellFalse.toNameEx).setTheory(CellTheory())
      } else {
        val tailState = shortCircuit(headState, tail)
        if (simplifier.isFalseConst(tailState.ex)) {
          // prune by propagating false
          tailState
        } else {
          // propagate
          var nextState = tailState.updateArena(_.appendCell(BoolT()))
          val pred = nextState.asCell.toNameEx
          rewriter.solverContext.assertGroundExpr(tla.equiv(pred, tla.and(headCell.toNameEx, tailState.ex)))
          nextState.setRex(pred).setTheory(CellTheory())
        }
      }
    }
  }
}
