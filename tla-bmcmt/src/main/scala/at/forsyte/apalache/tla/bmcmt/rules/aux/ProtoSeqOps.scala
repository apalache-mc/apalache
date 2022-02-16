package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.{CellT, UnknownT}
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir._

/**
 * Proto sequences that contain the absolute minimum for implementing TLA+ sequences. A proto sequence is essentially an
 * array of fixed size (which we call 'capacity'). A sequence is a pair that consists of the length (an integer cell)
 * and a proto sequence (a cell). The important property of the proto sequences is that they appear only in the arenas.
 * Hence, the complexity of iterative operations over proto sequences does not directly propagate to SMT. All operators
 * over sequences are expressible as operations over proto sequences, which makes proto sequences a nice layer of
 * abstraction.
 *
 * @param rewriter
 *   a symbolic rewriter
 * @author
 *   Igor Konnov
 */
class ProtoSeqOps(rewriter: SymbStateRewriter) {

  /**
   * Create a proto sequence of the given capacity and initialize its elements with the function `mkElem`.
   *
   * @param state
   *   a symbolic state to start with
   * @param capacity
   *   fixed capacity of the proto sequence
   * @param mkElem
   *   elements constructor receiving a state and an index-base-1
   * @return
   *   a new symbolic state and the cell of the proto sequence
   */
  def make(state: SymbState, capacity: Int, mkElem: (SymbState, Int) => (SymbState, ArenaCell)): SymbState = {
    // The proto sequence is a cell of unknown type, not introduced in SMT.
    val afterAppend = state.updateArena(_.appendCellNoSmt(UnknownT()))
    val protoSeq = afterAppend.arena.topCell

    // initialize the proto sequence with `mkElem`
    val (afterMk, cells) =
      capacity.to(1, -1).foldLeft((afterAppend, List[ArenaCell]())) { case ((s, createdCells), i) =>
        val (ns, cell) = mkElem(s, i)
        (ns, cell :: createdCells)
      }

    // attach the cells to the proto sequence, do not track this in SMT
    val nextState = afterMk.updateArena(_.appendHasNoSmt(protoSeq, cells: _*))
    nextState.setRex(protoSeq.toNameEx)
  }

  /**
   * Get the capacity of the proto sequence, that is, the number of cells allocated for the sequence elements.
   *
   * @param arena
   *   current arena
   * @param protoSeq
   *   a proto sequence
   * @return
   *   the number of cells that can fit into the sequence
   */
  def capacity(arena: Arena, protoSeq: ArenaCell): Int = {
    arena.getHas(protoSeq).length
  }

  /**
   * Retrieve the elements attached to the proto sequence. This is always a sequence of the [[capacity]]. If you need to
   * access a single element, use the method [[at]].
   *
   * @param arena
   *   the current arena
   * @param protoSeq
   *   a proto sequence
   * @return
   *   the sequence of cells that are attached to the proto sequence
   */
  def elems(arena: Arena, protoSeq: ArenaCell): Seq[ArenaCell] = {
    arena.getHas(protoSeq)
  }

  /**
   * Retrieve the ith element of the proto sequence. This operation does not produce any SMT constraints and it should
   * be used as much as possible instead of [[get]].
   *
   * @param arena
   *   the current arena
   * @param indexBase1
   *   a fixed index within the capacity
   * @return
   *   the cell that is attached to the index
   */
  def at(arena: Arena, protoSeq: ArenaCell, indexBase1: Int): ArenaCell = {
    val protoElems = elems(arena, protoSeq)
    if (indexBase1 < 1 || indexBase1 > protoElems.length) {
      throw new IllegalArgumentException(
          s"Implementation bug: Accessing proto sequence of size ${protoElems.length} with index ${indexBase1}")
    } else {
      protoElems(indexBase1 - 1)
    }
  }

  /**
   * Rewrite the index expression and access the element of the proto sequence. This operation produces `O(capacity)`
   * SMT constraints and it should be avoided, when possible. If the index is an integer literal, use [[at]].
   *
   * @param picker
   *   an instance of CherryPick that is used to pick the values
   * @param state
   *   a symbolic state to start with
   * @param defaultValue
   *   the value to return if the proto sequence has capacity of zero
   * @param indexBase1Ex
   *   an index expression (indices are starting with 1)
   * @return
   *   the new symbolic state that contains the retrieved cell as the expression
   */
  def get(picker: CherryPick, defaultValue: ArenaCell, state: SymbState, protoSeq: ArenaCell,
      indexBase1Ex: TlaEx): SymbState = {
    val protoElems = elems(state.arena, protoSeq)
    val capacity = protoElems.size
    if (capacity == 0) {
      // The sequence is statically empty. Return the default value.
      // Most likely, this expression will be never used as a result.
      state.setRex(defaultValue.toNameEx)
    } else {
      // rewrite `indexBase1Ex - 1` to a single cell
      var nextState = rewriter.rewriteUntilDone(state.setRex(tla.minus(indexBase1Ex, tla.int(1)) as IntT1()))
      val indexBase0 = nextState.asCell
      // create the oracle
      val (oracleState, oracle) = picker.oracleFactory.newIntOracle(nextState, capacity)
      // pick an element to be the result
      nextState = picker.pickByOracle(oracleState, oracle, protoElems, nextState.arena.cellTrue().toNameEx)
      val pickedResult = nextState.asCell
      // If 0 <= indexBase0 < capacity, then require oracle = indexBase0.
      // Otherwise, we do not restrict the outcome. This is consistent with Specifying Systems.
      // We do not refer to the actual length of the sequence (which we don't know).
      // Instead, we use the capacity of the proto sequence.
      val inRange =
        tla.and(tla.le(tla.int(0), indexBase0.toNameEx as IntT1()) as BoolT1(),
            tla.lt(indexBase0.toNameEx as IntT1(), tla.int(capacity)) as BoolT1()) as BoolT1()
      // (indexBase0 = oracle) <=> inRange
      val oracleEqArg = tla.eql(indexBase0.toNameEx, oracle.intCell.toNameEx as IntT1()) as IntT1() as BoolT1()
      val iff = tla.eql(oracleEqArg, inRange) as BoolT1()
      rewriter.solverContext.assertGroundExpr(iff)
      nextState.setRex(pickedResult.toNameEx)
    }
  }

  /**
   * Make a sequence out of a proto sequence.
   *
   * @param state
   *   a symbolic state to start with
   * @param seqT
   *   the type of the sequence
   * @param protoSeq
   *   a proto sequence
   * @param len
   *   a cell that encodes the actual length of the sequence
   * @return
   *   the new symbolic state that contains the created sequence as the expression
   */
  def mkSeq(state: SymbState, seqT: TlaType1, protoSeq: ArenaCell, len: ArenaCell): SymbState = {
    var nextState = state.updateArena(_.appendCell(CellT.fromType1(seqT)))
    val seq = nextState.arena.topCell
    // note that we do not track in SMT the relation between the sequence, the proto sequence, and its length
    nextState = nextState.updateArena(_.appendHasNoSmt(seq, len, protoSeq))
    nextState.setRex(seq.toNameEx)
  }

  /**
   * Retrieve the proto sequence from the sequence.
   *
   * @param arena
   *   the current arena
   * @param seq
   *   a sequence to extract the proto sequence from
   * @return
   *   the cell of the proto sequence
   */
  def fromSeq(arena: Arena, seq: ArenaCell): ArenaCell = {
    getLenAndProto(arena, seq)._2
  }

  /**
   * Retrieve the length of the sequence.
   *
   * @param arena
   *   the current arena
   * @param seq
   *   a sequence to extract the length from
   * @return
   *   the cell of the length
   */
  def seqLen(arena: Arena, seq: ArenaCell): ArenaCell = {
    getLenAndProto(arena, seq)._1
  }

  /**
   * Unpack a sequence into a commonly required triple: the proto sequence, the length cell, and capacity.
   *
   * @param arena
   *   the current arena
   * @param seq
   *   a sequence to unpack
   * @return
   *   (protoSequenceAsCell, lengthAsCell, capacity)
   */
  def unpackSeq(arena: Arena, seq: ArenaCell): (ArenaCell, ArenaCell, Int) = {
    val (len, protoSeq) = getLenAndProto(arena, seq)
    (protoSeq, len, capacity(arena, protoSeq))
  }

  /**
   * Fold-left the proto sequence with a binary operator that takes a state `state` and an element of the sequence
   * `elem` and produces the new state. The result is accumulated in `state.ex`. This function takes care of the case
   * when the length of the sequence is below the capacity.
   *
   * @param picker
   *   an instance of CherryPick that is used to pick the values
   * @param state
   *   a symbolic state to start with
   * @param protoSeq
   *   the proto sequence to fold
   * @param len
   *   the length encoded as a cell
   * @param binOp
   *   the binary operator that is applied to the accumulated result (in `state.ex`) and the element
   * @return
   *   the new symbolic state that contains the result of folding as an expression
   */
  def foldLeft(picker: CherryPick, state: SymbState, protoSeq: ArenaCell, len: ArenaCell,
      binOp: (SymbState, ArenaCell) => SymbState): SymbState = {
    // propagate the result only if the element is below the length
    def applyOne(state: SymbState, elem: ArenaCell, indexBase1: Int) = {
      // apply the operator, independently of whether we have reach the length or not (we don't know statically)
      var nextState = binOp(state, elem)
      val newResult = nextState.asCell
      // choose between the old result (if above the length) and the new result (if not above the length)
      val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(nextState, 2)
      nextState = picker
        .pickByOracle(oracleState, oracle, Seq(state.asCell, newResult), nextState.arena.cellTrue().toNameEx)
      val picked = nextState.ex
      val inRange = tla.le(tla.int(indexBase1), len.toNameEx as IntT1()) as BoolT1()
      val pickNew = oracle.whenEqualTo(nextState, 1) as BoolT1()
      val ite = tla.ite(inRange, pickNew, tla.not(pickNew) as BoolT1()) as BoolT1()
      rewriter.solverContext.assertGroundExpr(ite)

      nextState.setRex(picked)
    }

    // The rest is easy: Just fold over all elements.
    val elems = state.arena.getHas(protoSeq)
    elems.zipWithIndex.foldLeft(state) { case (s, (cell, indexBase0)) =>
      applyOne(s, cell, indexBase0 + 1)
    }
  }

  private def getLenAndProto(arena: Arena, seq: ArenaCell): (ArenaCell, ArenaCell) = {
    val cells = arena.getHas(seq)
    if (cells.length != 2) {
      throw new IllegalStateException(s"Corrupt sequence in the cell ${seq.id} of type ${seq.cellType}")
    } else {
      (cells.head, cells.tail.head)
    }
  }
}
