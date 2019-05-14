package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.TypeConverter
import at.forsyte.apalache.tla.bmcmt.types.{FinFunSetT, FinSetT, PowSetT}
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaSetOper

/**
  * Implements the rule: SE-FUNSET1, that is, constructs a function set [S -> T].
  *
  * @author Igor Konnov
   */
class FunSetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val typeConverter = new TypeConverter(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.funSet, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.funSet, domEx, cdmEx) =>
        // switch to cell theory
        var nextState = rewriter.rewriteUntilDone(state.setRex(domEx).setTheory(CellTheory()))
        nextState = convertIfNeeded(nextState)
        val dom = nextState.asCell
        nextState = rewriter.rewriteUntilDone(nextState.setRex(cdmEx).setTheory(CellTheory()))
        nextState = convertIfNeeded(nextState)
        val cdm = nextState.asCell
        val arena = nextState.arena.appendCell(FinFunSetT(dom.cellType, cdm.cellType))
        val newCell = arena.topCell
        val newArena = arena
          .setDom(newCell, dom)
          .setCdm(newCell, cdm)
        val finalState =
          state.setArena(newArena).setRex(newCell.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def convertIfNeeded(state: SymbState): SymbState = {
    val setCell = state.asCell
    setCell.cellType match {
      case FinSetT(_) => state

      case PowSetT(tp @ FinSetT(_)) =>
        typeConverter.convert(state, FinSetT(tp))

      case tp @ _ => throw new RewriterException("Unsupported domain/co-domain type: " + tp)
    }
  }
}
