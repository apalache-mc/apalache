package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx, TlaEx, ValEx}

/**
 * For state-level expressions, we express A \/ B as IF A THEN TRUE ELSE B.
 * For action-level expressions, i.e., involving primes, we do a direct translation to A \/ B.
 * This mimics the behavior of TLC.
 *
 * @author Igor Konnov
 */
class OrRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val boolTypes = Map("b" -> BoolT1())

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.or, _*) => true
      case _                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    val simplfier = new ConstSimplifierForSmt()
    simplfier.simplifyShallow(state.ex) match {
      case OperEx(TlaBoolOper.or, args @ _*) =>
        if (args.isEmpty) {
          // empty disjunction is always false
          state.setRex(state.arena.cellFalse().toNameEx)
        } else {
          // use short-circuiting on state-level expressions (like in TLC)
          def toIte(es: Seq[TlaEx]): TlaEx = {
            es match {
              case Seq(last) =>
                last

              case hd +: tail =>
                tla
                  .ite(hd ? "b", state.arena.cellTrue().toNameEx ? "b", toIte(tail))
                  .typed(boolTypes, "b")
            }
          }

          val newState =
            if (rewriter.config.shortCircuit) {
              // create a chain of IF-THEN-ELSE expressions and rewrite them
              state.setRex(toIte(args))
            } else {
              // simply translate to a disjunction
              var nextState = state.updateArena(_.appendCell(BoolT()))
              val pred = nextState.arena.topCell.toNameEx

              def mapArg(argEx: TlaEx): TlaEx = {
                nextState = rewriter.rewriteUntilDone(nextState.setRex(argEx))
                nextState.ex
              }

              val rewrittenArgs = args map mapArg
              val eq = tla
                .eql(pred ? "b", tla.or(rewrittenArgs: _*) ? "b")
                .typed(boolTypes, "b")
              rewriter.solverContext.assertGroundExpr(eq)
              nextState.setRex(pred)
            }

          rewriter.rewriteUntilDone(newState)
        }

      case e @ ValEx(_) =>
        // the simplifier has rewritten the disjunction to TRUE or FALSE
        rewriter.rewriteUntilDone(state.setRex(e))

      case e @ _ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, e), state.ex)
    }
  }
}
