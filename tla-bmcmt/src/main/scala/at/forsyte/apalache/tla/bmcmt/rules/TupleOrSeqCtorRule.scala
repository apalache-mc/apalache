package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * Rewrites a tuple or sequence constructor, that is, <<e_1, ..., e_k>>.
  * A tuple may be interpreted as a sequence, if it was properly type-annotated,
  * e.g., <<>> <: Seq(Int).
  *
  * @author Igor Konnov
  */
class TupleOrSeqCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.tuple, _*) => true
      case _                            => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.tuple, elems @ _*) =>
        // switch to cell theory
        val (stateAfterElems: SymbState, groundElems: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, elems)
        val cells = groundElems.map(stateAfterElems.arena.findCellByNameEx)

        // Get the resulting type from the type finder. It may happen to be a sequence!
        val resultT =
          rewriter.typeFinder.compute(state.ex, cells.map(_.cellType): _*)
        resultT match {
          case tt @ TupleT(_) => createTuple(stateAfterElems, tt, cells)
          case st @ SeqT(_)   => createSeq(stateAfterElems, st, cells)
          case _ =>
            throw new RewriterException("Unexpected type: " + resultT, state.ex)
        }

      case _ =>
        throw new RewriterException(
          "%s is not applicable".format(getClass.getSimpleName),
          state.ex
        )
    }
  }

  private def createTuple(
      state: SymbState,
      tupleT: TupleT,
      cells: Seq[ArenaCell]
  ): SymbState = {
    // create the tuple cell
    var arena = state.arena.appendCell(tupleT)
    val tuple = arena.topCell

    // connect the cells to the tuple (or a sequence): the order of edges is important!
    arena = arena.appendHasNoSmt(tuple, cells: _*)
    state.setArena(arena).setRex(tuple.toNameEx)
  }

  private def createSeq(
      state: SymbState,
      seqT: SeqT,
      cells: Seq[ArenaCell]
  ): SymbState = {
    // create a sequence cell
    var nextState = state.updateArena(_.appendCell(seqT))
    val seq = nextState.arena.topCell

    // connect N + 2 elements to seqT: the start (>= 0), the end (< len), and the sequence of values
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.int(0)))
    val start = nextState.asCell
    nextState =
      rewriter.rewriteUntilDone(nextState.setRex(tla.int(cells.length)))
    val end = nextState.asCell
    nextState =
      nextState.updateArena(_.appendHasNoSmt(seq, start +: end +: cells: _*))
    // we do not add SMT constraints as they are not important
    nextState.setRex(seq.toNameEx)
  }

}
