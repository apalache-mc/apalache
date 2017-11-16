package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
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
        def mkInCase(domElem: ArenaCell): TlaEx = {
          val inDomain = tla.in(domElem, domainCell)
          val funEqResult =
            tla.eql(resultCell, tla.appFun(funCell, domElem)) // translated as function application in SMT
          val eq = newArena.lazyEquality.mkEquality(newArena, domElem, argCell)
          tla.and(inDomain, eq, funEqResult)
        }
        // Equation (3): there is no domain element that equals to the argument
        def mkNotInCase(domElem: ArenaCell): TlaEx = {
          val notInDomain = tla.not(tla.in(domElem, domainCell))
          val notEqualToArgument = tla.not(newArena.lazyEquality.mkEquality(newArena, domElem, argCell))
          tla.or(notInDomain, notEqualToArgument)
        }

        val found = tla.or(newArena.getHas(domainCell).map(mkInCase): _*)
        val notFound = tla.and(newArena.getHas(domainCell).map(mkNotInCase): _*)
        newArena.solverContext.assertGroundExpr(tla.or(found, notFound))

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
