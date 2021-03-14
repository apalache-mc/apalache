package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.oper.TlaSeqOper

/**
 * Sequence operations: Head, Tail, Len, SubSeq, and Append.
 *
 * @author Igor Konnov
 */
class SeqOpsRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new CherryPick(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSeqOper.head, _)         => true
      case OperEx(TlaSeqOper.tail, _)         => true
      case OperEx(TlaSeqOper.subseq, _, _, _) => true
      case OperEx(TlaSeqOper.len, _)          => true
      case OperEx(TlaSeqOper.append, _, _)    => true
      case OperEx(TlaSeqOper.concat, _, _)    => true
      // TlaSeqOper.selectseq => ???
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSeqOper.head, seq) =>
        rewriter.rewriteUntilDone(state.setRex(tla.appFun(seq, tla.int(1))))

      case OperEx(TlaSeqOper.len, seq) =>
        translateLen(state, seq)

      case OperEx(TlaSeqOper.tail, seq) =>
        translateTail(state, seq)

      case OperEx(TlaSeqOper.subseq, seq, newStart, newEnd) =>
        translateSubSeq(state, seq, newStart, newEnd)

      case OperEx(TlaSeqOper.append, seq, newElem) =>
        translateAppend(state, seq, newElem)

      case OperEx(TlaSeqOper.concat, seq, otherSeq) =>
        translateConcat(state, seq, otherSeq)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def translateTail(state: SymbState, seq: TlaEx) = {
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq))
    val seqCell = nextState.asCell
    val cells = nextState.arena.getHas(seqCell)
    val start = cells.head
    val end = cells.tail.head
    // increment start, unless it goes over the bound
    val updatedStart =
      tla.ite(tla.lt(start.toNameEx, end.toNameEx), tla.plus(tla.int(1), start.toNameEx), start.toNameEx)
    // increment start
    nextState = rewriter.rewriteUntilDone(nextState.setRex(updatedStart))
    val newStart = nextState.asCell
    // introduce a new sequence that is different from seq in that the 0th element equals to newStart
    nextState = nextState.updateArena(_.appendCell(seqCell.cellType))
    val newSeqCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.appendHasNoSmt(newSeqCell, newStart +: cells.tail: _*))
    nextState.setRex(newSeqCell.toNameEx)
  }

  private def translateSubSeq(state: SymbState, seq: TlaEx, newStartEx: TlaEx, newEndEx: TlaEx) = {
    var nextState = state
    def rewriteToCell(ex: TlaEx): ArenaCell = {
      nextState = rewriter.rewriteUntilDone(nextState.setRex(ex))
      nextState.asCell
    }

    val seqCell = rewriteToCell(seq)
    val cells = nextState.arena.getHas(seqCell)
    val start = cells.head
    val end = cells.tail.head

    // compute the new interval [expectedStart, expectedEnd)
    val expectedStart = rewriteToCell(tla.plus(start.toNameEx, tla.minus(newStartEx, tla.int(1))))
    val expectedEnd = rewriteToCell(tla.plus(start.toNameEx, newEndEx))
    // use the computed values, as soon as they do not violate the invariant:
    //   start <= end, start >= oldStart, end <= oldEnd
    val seqInvariant = rewriteToCell(
        tla.and(
            tla.le(expectedStart.toNameEx, expectedEnd.toNameEx),
            tla.le(start.toNameEx, expectedStart.toNameEx),
            tla.le(expectedEnd.toNameEx, end.toNameEx)
        ))

    val newStart = rewriteToCell(tla.ite(seqInvariant.toNameEx, expectedStart.toNameEx, tla.int(0)))
    val newEnd = rewriteToCell(tla.ite(seqInvariant.toNameEx, expectedEnd.toNameEx, tla.int(0)))

    // introduce a new sequence that whose start and end are updated as required
    nextState = nextState.updateArena(_.appendCell(seqCell.cellType))
    val newSeqCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.appendHasNoSmt(newSeqCell, newStart :: newEnd +: cells.tail.tail: _*))
    nextState.setRex(newSeqCell.toNameEx)
  }

  private def translateAppend(state: SymbState, seq: TlaEx, newElem: TlaEx) = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq))
    val seqCell = nextState.asCell
    val cells = nextState.arena.getHas(seqCell)
    val start = cells.head
    val end = cells.tail.head
    val oldElems = cells.tail.tail
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.plus(tla.int(1), end.toNameEx)))
    val newEnd = nextState.asCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(newElem))
    val newElemCell = nextState.asCell
    // as we do not know the actual values of the range [start, end),
    // pick from the original value s[i] and the new element, and restrict the choice
    // based on the actual values of start and end
    def transform(oldElemCell: ArenaCell, no: Int): ArenaCell = {
      val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(nextState, 2)
      nextState = oracleState
      nextState = picker.pickByOracle(nextState, oracle, Seq(oldElemCell, newElemCell),
          nextState.arena.cellTrue().toNameEx)
      // pick the element from the old sequence: start <= no /\ no < end => oracle = 0
      solverAssert(tla.impl(tla.and(tla.le(start.toNameEx, tla.int(no)), tla.lt(tla.int(no), end.toNameEx)),
              oracle.whenEqualTo(nextState, 0)))
      // pick the element from the new sequence: no = end => oracle = 1
      solverAssert(tla.impl(tla.eql(tla.int(no), end.toNameEx), oracle.whenEqualTo(nextState, 1)))
      // the other elements are unrestricted, give some freedom to the solver
      nextState.asCell
    }

    val transformedCells = oldElems.zipWithIndex map (transform _).tupled
    val newCells = (newElemCell :: transformedCells.reverse).reverse

    // introduce a new sequence that statically has one more element
    nextState = nextState.updateArena(_.appendCell(seqCell.cellType))
    val newSeqCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.appendHasNoSmt(newSeqCell, start :: newEnd +: newCells: _*))
    nextState.setRex(newSeqCell.toNameEx)
  }

  private def translateLen(state: SymbState, seq: TlaEx) = {
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq))
    val cells = nextState.arena.getHas(nextState.asCell)
    val start = cells.head
    val end = cells.tail.head
    // just return end - start
    rewriter.rewriteUntilDone(nextState.setRex(tla.minus(end.toNameEx, start.toNameEx)))
  }

  // Implement concatenation on sequences. This is the most expensive operation on sequences.
  private def translateConcat(state: SymbState, seq1: TlaEx, seq2: TlaEx): SymbState = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _

    var nextState = state

    def rewriteSeq(seqEx: TlaEx): (ArenaCell, ArenaCell, ArenaCell, Seq[ArenaCell], CellT) = {
      nextState = rewriter.rewriteUntilDone(nextState.setRex(seqEx))
      val cell = nextState.asCell
      val connectedCells = nextState.arena.getHas(cell)
      val start = connectedCells.head
      val end = connectedCells.tail.head
      val elems = connectedCells.tail.tail
      nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.minus(end.toNameEx, start.toNameEx)))
      val len = nextState.asCell
      (start, end, len, elems, cell.cellType)
    }

    // rewrite the expressions
    val (start1, end1, len1, elems1, cellType) = rewriteSeq(seq1)
    val (start2, end2, len2, elems2, _) = rewriteSeq(seq2)

    // introduce a new sequence
    nextState = nextState.updateArena(_.appendCell(cellType))
    val seq3 = nextState.arena.topCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.int(0)))
    val start3 = nextState.asCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.plus(len1.toNameEx, len2.toNameEx)))
    val end3 = nextState.asCell

    val elems1then2 = elems1 ++ elems2
    val ntotal = elems1then2.length

    // pre-compute integer constants that are used when computing every element
    // offset2 = N1 + start2 - len1
    nextState = rewriter
      .rewriteUntilDone(nextState.setRex(tla.minus(tla.plus(tla.int(elems1.size), start2.toNameEx), len1.toNameEx)))
    val offset2 = nextState.asCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.plus(len1.toNameEx, len2.toNameEx)))
    val len1plus2 = nextState.asCell

    // introduce constraints for the i-th element of the resulting sequence
    def pickElem(i: Int): ArenaCell = {
      // create the oracle
      val (oracleState, oracle) = picker.oracleFactory.newIntOracle(nextState, ntotal + 1)
      nextState = oracleState
      // pick an element to be the result
      nextState = picker.pickByOracle(nextState, oracle, elems1then2, nextState.arena.cellTrue().toNameEx)
      val pickedResult = nextState.asCell
      // If 0 <= i < len1, then require oracle = i + start1,
      // If len1 <= i < len1 + len2, then require oracle = i + offset2 = i - len1 + N1 + start2,
      // Otherwise, set oracle to N
      val inRange1 = tla.lt(tla.int(i), len1.toNameEx)
      val inRange2 =
        tla.and(tla.le(len1.toNameEx, tla.int(i)), tla.lt(tla.int(i), len1plus2.toNameEx))

      val whenInRange1 =
        tla.or(tla.not(inRange1), tla.eql(oracle.intCell.toNameEx, tla.plus(tla.int(i), start1.toNameEx)))
      val whenInRange2 =
        tla.or(tla.not(inRange2), tla.eql(oracle.intCell.toNameEx, tla.plus(tla.int(i), offset2.toNameEx)))
      val whenOutOfRange =
        tla.or(tla.lt(tla.int(i), len1plus2.toNameEx), tla.eql(oracle.intCell.toNameEx, tla.int(ntotal)))

      solverAssert(whenInRange1)
      solverAssert(whenInRange2)
      solverAssert(whenOutOfRange)

      pickedResult
    }

    val newCells: Seq[ArenaCell] = 0.until(ntotal) map pickElem

    // finally, add start, end, and the elements to the sequence
    nextState = nextState.updateArena(_.appendHasNoSmt(seq3, start3 +: end3 +: newCells: _*))

    nextState.setRex(seq3.toNameEx)
  }

}
