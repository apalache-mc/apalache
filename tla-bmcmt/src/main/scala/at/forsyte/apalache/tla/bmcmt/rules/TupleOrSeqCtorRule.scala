package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.ProtoSeqOps
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{OperEx, SeqT1, TlaEx, TupT1}

/**
 * Rewrites a tuple or sequence constructor, that is, <<e_1, ..., e_k>>. A tuple may be interpreted as a sequence, if it
 * was properly type-annotated.
 *
 * @author
 *   Igor Konnov
 */
class TupleOrSeqCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val proto = new ProtoSeqOps(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.tuple, _*) => true
      case _                            => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaFunOper.tuple, elems @ _*) =>
        // rewrite all elements
        val (stateAfterElems: SymbState, groundElems: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, elems)
        val cells = groundElems.map(stateAfterElems.arena.findCellByNameEx)

        // Get the resulting type from the type tag. It may be either a sequence or a tuple.
        val resultT = CellT.fromTypeTag(ex.typeTag)
        resultT match {
          case CellTFrom(tt @ TupT1(_ @_*)) => createTuple(stateAfterElems, tt, cells)
          case CellTFrom(st @ SeqT1(_))     => createSeq(stateAfterElems, st, cells)
          case _                            => throw new RewriterException("Unexpected type: " + resultT, state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def createTuple(state: SymbState, tupleT: TupT1, cells: Seq[ArenaCell]): SymbState = {
    // create the tuple cell
    var arena = state.arena.appendCell(tupleT)
    val tuple = arena.topCell

    // connect the cells to the tuple (or a sequence): the order of edges is important!
    arena = arena.appendHasNoSmt(tuple, cells.map(FixedElemPtr): _*)
    state.setArena(arena).setRex(tuple.toNameEx)
  }

  private def createSeq(state: SymbState, seqT: SeqT1, cells: Seq[ArenaCell]): SymbState = {
    // initialize the proto sequence with the elements
    def mkElem(s: SymbState, indexBase1: Int): (SymbState, ArenaCell) = (s, cells(indexBase1 - 1))

    var nextState = proto.make(state, cells.length, mkElem)
    val newProtoSeq = nextState.asCell
    // create the cell to store length
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.int(cells.length)))
    // create the sequence out of the proto sequence and its length
    proto.mkSeq(nextState, seqT, newProtoSeq, nextState.asCell)
  }

}
