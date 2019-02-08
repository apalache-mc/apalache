package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.caches.IntRangeCache
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * Implements the rules: SE-DOM.
  *
  * @author Igor Konnov
  */
class DomainRule(rewriter: SymbStateRewriter, intRangeCache: IntRangeCache) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.domain, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.domain, funEx) =>
        val funState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(funEx))
        val funCell = funState.asCell

        // no type information from the type finder is needed, as types are propagated in a straightforward manner
        val finalState =
          funCell.cellType match {
            case RecordT(_) | SeqT(_) =>
              val dom = funState.arena.getDom(funCell)
              funState.setRex(dom.toNameEx)

            case TupleT(_) =>
              mkTupleDomain(funState, funCell)

            case FunT(_, _) =>
              mkFunDomain(funState, funCell)

            case _ =>
              throw new RewriterException("DOMAIN x where type(x) = %s is not implemented".format(funCell.cellType))
          }

        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def mkTupleDomain(state: SymbState, funCell: ArenaCell): SymbState = {
    val tupleT = funCell.cellType.asInstanceOf[TupleT]
    val (newArena, dom) = intRangeCache.create(state.arena, (1, tupleT.args.size))
    state.setArena(newArena).setRex(dom.toNameEx).setTheory(CellTheory())
  }

  private def mkFunDomain(state: SymbState, funCell: ArenaCell): SymbState = {
    // the expression cache should help us here
    val relation = state.arena.getCdm(funCell)
    var nextState = state.appendArenaCell(FinSetT(funCell.cellType.asInstanceOf[FunT].argType))
    val domCell = nextState.arena.topCell
    def getArg(c: ArenaCell): ArenaCell = nextState.arena.getHas(c).head
    val domCells = nextState.arena.getHas(relation) map getArg
    nextState = nextState.setArena(nextState.arena.appendHas(domCell, domCells))
    for (pair <- state.arena.getHas(relation)) {
      val arg = getArg(pair)
      val iff = tla.equiv(tla.in(arg.toNameEx, domCell.toNameEx),
                          tla.in(pair.toNameEx, relation.toNameEx))
      rewriter.solverContext.assertGroundExpr(iff)
    }

    nextState.setRex(domCell.toNameEx)
  }
}
