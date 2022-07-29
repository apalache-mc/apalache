package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._

object FunOps {

  def constrainRelationArgs(
      state: SymbState,
      rewriter: SymbStateRewriter,
      domain: ArenaCell,
      relation: ArenaCell): SymbState = {

    rewriter.solverContext.config.smtEncoding match {
      case SMTEncoding.ArraysFun =>
        var nextState = state
        val domainElems = nextState.arena.getHas(domain)
        val relationElems = nextState.arena.getHas(relation)

        def eqAndInDomain(domainElem: ArenaCell, checkedElem: ArenaCell) = {
          val eq = rewriter.lazyEq.safeEq(domainElem, checkedElem)
          val selectInSet = tla.apalacheSelectInSet(domainElem.toNameEx, domain.toNameEx)
          tla.and(eq, selectInSet)
        }

        def isInDomain(elem: ArenaCell): TlaEx = {
          if (domainElems.isEmpty) {
            ValEx(TlaBool(false))
          } else {
            val elemInDomain = domainElems.zipAll(List(), elem, elem).map(zip => eqAndInDomain(zip._1, zip._2))
            tla.or(elemInDomain: _*)
          }
        }

        for (tuple <- relationElems) {
          val funArg = nextState.arena.getHas(tuple).head
          val argInDomain = tla.apalacheSelectInSet(funArg.toNameEx, domain.toNameEx)
          nextState = rewriter.lazyEq.cacheEqConstraints(nextState, domainElems.map((_, funArg)))
          rewriter.solverContext.declareInPredIfNeeded(domain, funArg)
          rewriter.solverContext.assertGroundExpr(OperEx(TlaBoolOper.equiv, argInDomain, isInDomain(funArg)))
        }

        nextState

      case _ =>
        state
    }
  }
}
