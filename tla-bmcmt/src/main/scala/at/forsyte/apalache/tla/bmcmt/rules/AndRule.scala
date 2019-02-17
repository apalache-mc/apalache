package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
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
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.and, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    val falseConst = SolverContext.falseConst
    val trueConst = SolverContext.trueConst
    val simplifier = new ConstSimplifier()
    simplifier.simplifyShallow(state.ex) match {
      case OperEx(TlaBoolOper.and, args @ _*) =>
        val finalState =
          if (args.isEmpty) {
            // empty conjunction is always true
            state.setRex(NameEx(trueConst)).setTheory(BoolTheory())
          } else {
            // use short-circuiting on state-level expressions (like in TLC)
            def toIte(es: Seq[TlaEx]): TlaEx = {
              es match {
                case Seq(last) => last
                case hd +: tail => tla.ite(hd, toIte(tail), NameEx(falseConst))
              }
            }
            // create a chain of IF-THEN-ELSE expressions and rewrite them
            val newState = state.setRex(toIte(args)).setTheory(CellTheory())
            rewriter.rewriteUntilDone(newState)
          }

        rewriter.coerce(finalState, state.theory) // coerce if needed

      case e @ ValEx(_) =>
        // the simplifier has rewritten the disjunction to TRUE or FALSE
        rewriter.rewriteUntilDone(state.setRex(e))

      case e @ _ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, e))
    }
  }
}
