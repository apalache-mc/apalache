package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-FUN-APP[1-3].
  *
  * @author Igor Konnov
  */
class FunAppRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new PickFromAndFunMerge(rewriter)

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

        val resState = picker.pick(codomainCell, argState)

        // SE-FUN-APP3
        val resultCell = resState.ex
        val domCells = resState.arena.getHas(domainCell)

        // cache equalities
        val eqState = rewriter.lazyEq.cacheEqConstraints(resState, domCells.map(e => (e, argCell)))

        // Equation (2): there is a domain element that equals to the argument
        def mkInCase(domElem: ArenaCell): TlaEx = {
          val inDomain = tla.in(domElem, domainCell)
          val funEqResult =
            tla.eql(resultCell, tla.appFun(funCell, domElem)) // translated as function application in SMT
          val eq = rewriter.lazyEq.safeEq(domElem, argCell) // just use SMT equality
          tla.and(inDomain, eq, funEqResult)
        }

        // Equation (3): there is no domain element that equals to the argument
        def mkNotInCase(domElem: ArenaCell): TlaEx = {
          val notInDomain = tla.not(tla.in(domElem, domainCell))
          val eq = rewriter.lazyEq.safeEq(domElem, argCell) // just use SMT equality
          tla.or(notInDomain, tla.not(eq))
        }

        val found = tla.or(domCells.map(mkInCase): _*)
        val eqFailure = tla.eql(resultCell, eqState.arena.cellFailure())
        val notFound = tla.and(eqFailure, tla.and(domCells.map(mkNotInCase): _*))
        eqState.arena.solverContext.assertGroundExpr(tla.or(found, notFound))

        val finalState = eqState
          .setTheory(CellTheory())
          .setRex(resultCell)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

}
