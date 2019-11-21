package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

/**
  * For state-level expressions, we express A \/ B as IF A THEN TRUE ELSE B.
  * For action-level expressions, i.e., involving primes, we do a direct translation to A \/ B.
  * This mimics the behavior of TLC.
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
    val falseConst = SolverContext.falseConst
    val trueConst = SolverContext.trueConst
    val simplfier = new ConstSimplifierForSmt()
    simplfier.simplifyShallow(state.ex) match {
      case OperEx(TlaBoolOper.or, args@_*) =>
        val finalState =
          if (args.isEmpty) {
            // empty disjunction is always false
            state.setRex(NameEx(falseConst)).setTheory(BoolTheory())
          } else {
            // use short-circuiting on state-level expressions (like in TLC)
            def toIte(es: Seq[TlaEx]): TlaEx = {
              es match {
                case Seq(last) => last
                case hd +: tail => tla.ite(hd, NameEx(trueConst), toIte(tail))
              }
            }

            val newState =
              if (rewriter.config.shortCircuit) {
                // create a chain of IF-THEN-ELSE expressions and rewrite them
                state.setRex(toIte(args)).setTheory(BoolTheory())
              } else {
                // simply translate to a disjunction
                var nextState = state.updateArena(_.appendCell(BoolT()))
                val pred = nextState.arena.topCell.toNameEx
                def mapArg(argEx: TlaEx): TlaEx = {
                  nextState = rewriter.rewriteUntilDone(nextState.setRex(argEx).setTheory(CellTheory()))
                  nextState.ex
                }

                val rewrittenArgs = args map mapArg
                rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.or(rewrittenArgs :_*)))
                nextState.setRex(pred).setTheory(CellTheory())
              }

            rewriter.rewriteUntilDone(newState)
          }

        rewriter.coerce(finalState, state.theory) // coerce if needed

      case e@ValEx(_) =>
        // the simplifier has rewritten the disjunction to TRUE or FALSE
        rewriter.rewriteUntilDone(state.setRex(e))

      case e@_ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, e))
    }
  }
}
