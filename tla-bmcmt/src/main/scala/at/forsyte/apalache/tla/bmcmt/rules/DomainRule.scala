package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.caches.IntRangeCache
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Rewriting DOMAIN f, that is, translating the domain of a function, record, tuple, or sequence.
 *
 * @author
 *   Igor Konnov
 */
class DomainRule(rewriter: SymbStateRewriter, intRangeCache: IntRangeCache) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.domain, _) => true
      case _                            => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.domain, funEx) =>
        val funState = rewriter.rewriteUntilDone(state.setRex(funEx))
        val funCell = funState.asCell

        // no type information from the type finder is needed, as types are propagated in a straightforward manner
        funCell.cellType match {
          case RecordT(_) =>
            val dom = funState.arena.getDom(funCell)
            funState.setRex(dom.toNameEx)

          case TupleT(_) =>
            mkTupleDomain(funState, funCell)

          case SeqT(_) =>
            mkSeqDomain(funState, funCell)

          case FunT(_, _) =>
            mkFunDomain(funState, funCell)

          case _ =>
            throw new RewriterException("DOMAIN x where type(x) = %s is not implemented".format(funCell.cellType),
                state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def mkTupleDomain(state: SymbState, funCell: ArenaCell): SymbState = {
    val tupleT = funCell.cellType.asInstanceOf[TupleT]
    val (newArena, dom) = intRangeCache.create(state.arena, (1, tupleT.args.size))
    state.setArena(newArena).setRex(dom.toNameEx)
  }

  private def mkSeqDomain(state: SymbState, seqCell: ArenaCell): SymbState = {
    // as we do not know the domain precisely, we create the set 1..N and include only its elements between start and end
    val start :: end +: elems = state.arena.getHas(seqCell)
    val (newArena, staticDom) = intRangeCache.create(state.arena, (1, elems.size))
    // we cannot use staticDom directly, as its in-relation is restricted, create a copy
    var arena = newArena.appendCell(staticDom.cellType)
    val dom = arena.topCell
    arena = arena.appendHas(dom, arena.getHas(staticDom): _*)
    for (domElem <- arena.getHas(staticDom)) {
      val inDom = tla.apalacheStoreInSet(domElem.toNameEx, dom.toNameEx)
      // note that start >=0 and end equals the last element, so use start < domElem and domElem <= end
      val inRange = tla.and(tla.lt(start.toNameEx, domElem.toNameEx), tla.le(domElem.toNameEx, end.toNameEx))
      rewriter.solverContext.assertGroundExpr(tla.eql(inDom, inRange))
    }

    state.setArena(arena).setRex(dom.toNameEx)
  }

  private def mkFunDomain(state: SymbState, funCell: ArenaCell): SymbState = {
    // We are computing the domain every time. Although the expression cache should help us,
    // it probably makes sense to cache the domain, once it has been computed.
    // Function domain is tricky, as it is a left projection of the function relation.
    // The function relation may contain ghost pairs, which are marked as being outside of the relation.
    // Hence, we group the pairs into a map: key |-> list of pairs. Then, we include the key into the domain
    // if and only if at least one of the pairs belongs to the relation.
    val relation = state.arena.getCdm(funCell)
    var nextState = state.updateArena(_.appendCell(FinSetT(funCell.cellType.asInstanceOf[FunT].argType)))
    val domCell = nextState.arena.topCell

    def getArg(c: ArenaCell): ArenaCell = nextState.arena.getHas(c).head

    val pairs = nextState.arena.getHas(relation)
    // importantly, add `domCells` to a set, to avoid duplicate cells (different cells still may be equal)
    val domCells = pairs.map(getArg).toSet.toSeq
    // construct a map from cell ids to lists of pairs
    type KeyToPairs = Map[Int, Set[ArenaCell]]

    def addPair(map: KeyToPairs, pair: ArenaCell): KeyToPairs = {
      val key = getArg(pair)
      val pairsForKey = map.getOrElse(key.id, Set.empty) + pair
      map + (key.id -> pairsForKey)
    }

    val keysToPairs = pairs.foldLeft(Map[Int, Set[ArenaCell]]())(addPair)

    // add the cells, some of which may be ghost cells
    nextState = nextState.updateArena(_.appendHas(domCell, domCells: _*))
    for (pairsForKey <- keysToPairs.values) {
      val head = pairsForKey.head
      val keyCell = getArg(head)
      val isMem =
        if (pairsForKey.size == 1) {
          // 1. The trivial case: The cell appears only once.
          tla.apalacheSelectInSet(head.toNameEx, relation.toNameEx)
        } else {
          // 2. The hard case: The cell appears in multiple pairs, some of them may be ghost cells.
          tla.or(pairsForKey.toSeq.map(p => tla.apalacheSelectInSet(p.toNameEx, relation.toNameEx).untyped()): _*)
        }

      val ite = tla.ite(isMem, tla.apalacheStoreInSet(keyCell.toNameEx, domCell.toNameEx),
          tla.apalacheStoreNotInSet(keyCell.toNameEx, domCell.toNameEx))
      rewriter.solverContext.assertGroundExpr(ite)
    }

    nextState.setRex(domCell.toNameEx)
  }
}
