package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.caches.IntRangeCache
import at.forsyte.apalache.tla.bmcmt.rules.aux.{ProtoSeqOps, RecordOps}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs.{tlaExToBuilderExAsTyped, BuilderExAsTyped}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir._

/**
 * Rewriting DOMAIN f, that is, translating the domain of a function, record, tuple, or sequence.
 *
 * @author
 *   Igor Konnov
 */
class DomainRule(rewriter: SymbStateRewriter, intRangeCache: IntRangeCache) extends RewritingRule {
  private val proto = new ProtoSeqOps(rewriter)
  private val recordOps = new RecordOps(rewriter)

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

        funCell.cellType match {
          case CellTFrom(RecT1(_)) =>
            val dom = funState.arena.getDom(funCell)
            funState.setRex(dom.toNameEx)

          case CellTFrom(RecRowT1(_)) =>
            recordOps.domain(funState, funCell)

          case CellTFrom(tt @ TupT1(_ @_*)) =>
            mkTupleDomain(funState, tt)

          case CellTFrom(SeqT1(_)) =>
            mkSeqDomain(funState, funCell)

          case CellTFrom(FunT1(_, _)) =>
            mkFunDomain(funState, funCell)

          case _ =>
            throw new RewriterException("DOMAIN x where type(x) = %s is not implemented".format(funCell.cellType),
                state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  protected def mkTupleDomain(state: SymbState, tupleT: TupT1): SymbState = {
    val (newArena, dom) = intRangeCache.create(state.arena, (1, tupleT.elems.size))
    state.setArena(newArena).setRex(dom.toNameEx)
  }

  protected def mkSeqDomain(state: SymbState, seqCell: ArenaCell): SymbState = {
    val (protoSeq @ _, len, capacity) = proto.unpackSeq(state.arena, seqCell)
    // We do not know the domain precisely, as it depends on the length of the sequence.
    // Hence, we create the set `1..capacity` and include only those elements that are not greater than `len`.
    val (newArena, staticDom) = intRangeCache.create(state.arena, (1, capacity))
    // we cannot use staticDom directly, as its in-relation is restricted, create a copy
    var arena = newArena.appendCellOld(staticDom.cellType)
    val dom = arena.topCell
    arena = arena.appendHas(dom, arena.getHas(staticDom): _*)
    for ((domElem, indexBase0) <- arena.getHas(staticDom).zipWithIndex) {
      val inDom = tla.apalacheStoreInSet(domElem.toNameEx, dom.toNameEx)
      val notInDom = tla.apalacheStoreNotInSet(domElem.toNameEx, dom.toNameEx)
      // the element is in range, if indexBase0 < len
      val inRange = tla.lt(tla.int(indexBase0), len.toNameEx.as(IntT1)).as(BoolT1)
      rewriter.solverContext.assertGroundExpr(tla.ite(inRange, inDom, notInDom))
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
    var nextState = state.updateArena(_.appendCell(SetT1(funCell.cellType.toTlaType1.asInstanceOf[FunT1].arg)))
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
