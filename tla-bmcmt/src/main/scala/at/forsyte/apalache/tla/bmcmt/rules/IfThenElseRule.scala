package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, ConstT, IntT}
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.convenience._


/**
  * Implements the rules: SE-ITE[1-5].
  *
  * @author Igor Konnov
  */
class IfThenElseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaControlOper.ifThenElse, _, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        val predState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()).setRex(predEx))
        val thenState = rewriter.rewriteUntilDone(predState.setTheory(CellTheory()).setRex(thenEx))
        val elseState = rewriter.rewriteUntilDone(thenState.setTheory(CellTheory()).setRex(elseEx))
        val thenCell = elseState.arena.findCellByNameEx(thenState.ex)
        val elseCell = elseState.arena.findCellByNameEx(elseState.ex)
        val pred = predState.ex
        (thenCell.cellType, elseCell.cellType) match {
          case (BoolT(), BoolT()) | (IntT(), IntT()) | (ConstT(), ConstT()) =>
            val newArena = elseState.arena.appendCell(thenCell.cellType)
            val newCell = newArena.topCell
            // it's OK to use the SMT equality, as we are dealing with the basic types here
            val ifCond = tla.and(pred, tla.eql(newCell, thenCell))
            val elseCond = tla.and(tla.not(pred), tla.eql(newCell, elseCell))
            rewriter.solverContext.assertGroundExpr(tla.or(ifCond, elseCond))
            val finalState = elseState
                .setArena(newArena)
                .setRex(newCell.toNameEx)
            rewriter.coerce(finalState, state.theory)

          case _ =>
            throw new RewriterException("Attempting to apply IF-THEN-ELSE to %s and %s, not supported"
              .format(thenCell.cellType, elseCell.cellType))
        }


      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
