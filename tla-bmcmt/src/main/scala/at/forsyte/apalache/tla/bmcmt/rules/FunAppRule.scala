package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-FUN-APP[1-3].
  *
  * @author Igor Konnov
  */
class FunAppRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.app, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.app, funEx, argEx) =>
        // SE-FUN-APP1
        val funState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(funEx))
        // SE-FUN-APP2
        val argState = rewriter.rewriteUntilDone(funState.setTheory(CellTheory()).setRex(argEx))
        val funCell = argState.arena.findCellByNameEx(funState.ex)
        val argCell = argState.arena.findCellByNameEx(argState.ex)
        val domainCell = argState.arena.getDom(funCell)
        val codomainCell = argState.arena.getCdm(funCell)

        val resultType = codomainCell.cellType match {
          case FinSetT(ConstT()) => ConstT()
          case FinSetT(IntT()) => IntT()
          case FinSetT(BoolT()) => BoolT()

          case _ =>
            throw new RewriterException("TODO: only basic types are supported as a function result")
        }
        // SE-FUN-APP3
        val newArena = argState.arena.appendCell(resultType)
        val resultCell = newArena.topCell
        // Equation (2): there is a domain element that equals to the argument
        def mkElemCase(domElem: ArenaCell): TlaEx = {
          val inDomain = OperEx(TlaSetOper.in, domElem.toNameEx, domainCell.toNameEx)
          val eq = newArena.lazyEquality.mkEquality(newArena, domElem, argCell)
          val funEqResult = OperEx(TlaOper.eq,
            resultCell.toNameEx,
            OperEx(TlaFunOper.app, funCell.toNameEx, domElem.toNameEx)) // this is translated as a function application
          OperEx(TlaBoolOper.and, inDomain, eq, funEqResult)
        }
        val elemCells = newArena.getHas(domainCell)
        newArena.solverContext.assertGroundExpr(OperEx(TlaBoolOper.or, elemCells.map(mkElemCase): _*))
        // TODO: account for Equation (3), that is, the argument is not equal to any domain element

        val finalState = argState
          .setTheory(CellTheory())
          .setRex(resultCell.toNameEx)
          .setArena(newArena)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("FunAppRule is not applicable")
    }
  }

}
