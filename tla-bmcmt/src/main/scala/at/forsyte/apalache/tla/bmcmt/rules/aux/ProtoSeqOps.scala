package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.{CellT, UnknownT}
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.ArraySeq

/**
 * <p>Proto sequences that contain the absolute minimum for implementing TLA+ sequences. A proto sequence is a
 * collection of cells, which are ordered by indices 1, ..., `capacity`. Importantly, `capacity` is a static value,
 * which does not have to be tracked symbolically. The important property of the proto sequences is that they appear
 * only in the arenas. Hence, the complexity of iterative operations over proto sequences does not directly propagate to
 * SMT.</p>
 *
 * <p>A TLA+ sequence is represented with a pair that consists of the length (an integer cell) and a proto sequence (a
 * cell). All operators over sequences are expressible as operations over proto sequences, which makes proto sequences a
 * nice layer of abstraction.</p>
 *
 * <p>This class effectively defines an abstract data type. We call it `ProtoSeqOps` to reflect that the instances of
 * this class are not objects of this datatype but a set of functions over proto sequences.</p>
 *
 * @param rewriter
 *   a symbolic rewriter
 * @author
 *   Igor Konnov
 */
class ProtoSeqOps(rewriter: SymbStateRewriter) {

  /**
   * Create a proto sequence of the given capacity and initialize its elements with the function `mkElem`. It is
   * important that `mkElem` is free of side effects.
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
    // introduce an array to initialize the cells
    val cellsAsArray = new Array[ArenaCell](capacity)
    // initialize the elements with `mkElem`
    var nextState =
      1.to(capacity).foldLeft(state) { case (currentState, i) =>
        val (changedState, cell) = mkElem(currentState, i)
        cellsAsArray(i - 1) = cell
        changedState
      }

    // The proto sequence is a cell of unknown type, not introduced in SMT.
    nextState = nextState.updateArena(_.appendCellNoSmt(UnknownT()))
    val protoSeq = nextState.arena.topCell

    // attach the cells to the proto sequence, do not track this in SMT
    nextState = nextState.updateArena(_.appendHasNoSmt(protoSeq, ArraySeq.unsafeWrapArray(cellsAsArray): _*))
    nextState.setRex(protoSeq.toNameEx)
  }

  /**
   * Create a cell that encodes a proto sequence of capacity 0.
   *
   * @param arena
   *   an arena to start with
   * @return
   *   the new arena and the fresh cell that holds the proto sequence
   */
  def makeEmptyProtoSeq(arena: Arena): (Arena, ArenaCell) = {
    val newArena = arena.appendCellNoSmt(UnknownT())
    (newArena, newArena.topCell)
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
   * Retrieve the elements attached to the proto sequence. This is a Scala list that contains exactly [[capacity]]
   * cells. If you need to access a single element, use the method [[at]].
   *
   * @param arena
   *   the current arena
   * @param protoSeq
   *   a proto sequence
   * @return
   *   the list of cells that are attached to the proto sequence
   */
  def elems(arena: Arena, protoSeq: ArenaCell): List[ArenaCell] = {
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
  def get(
      picker: CherryPick,
      defaultValue: ArenaCell,
      state: SymbState,
      protoSeq: ArenaCell,
      indexBase1Ex: TlaEx): SymbState = {
    val protoElems = elems(state.arena, protoSeq)
    val capacity = protoElems.length
    if (capacity == 0) {
      // The sequence is statically empty. Return the default value.
      // Most likely, this expression will be never used as a result.
      state.setRex(defaultValue.toNameEx)
    } else {
      // rewrite `indexBase1Ex` to a single cell
      var nextState = rewriter.rewriteUntilDone(state.setRex(indexBase1Ex))
      val indexCellBase1 = nextState.asCell

      rewriter.intValueCache.findKey(indexCellBase1) match {
        case None =>
          // The general case: we cannot statically predict the value of indexCell.
          // Hence, we have to pick one of the sequence elements and restrict it with an oracle.
          // This introduces O(capacity) constraints.
          val (oracleState, oracle) = picker.oracleFactory.newIntOracle(nextState, capacity)
          // pick an element to be the result
          nextState = picker.pickByOracle(oracleState, oracle, protoElems, nextState.arena.cellTrue().toNameEx)
          val pickedResult = nextState.asCell
          val indexCellBase1asInt = indexCellBase1.toNameEx.as(IntT1())
          // If 0 < indexCell <= capacity, then require oracle = indexCell - 1.
          // Otherwise, we do not restrict the outcome. This is consistent with Specifying Systems.
          // We do not refer to the actual length of the sequence (which we don't know).
          // Instead, we use the capacity of the proto sequence.
          val inRange =
            tla
              .and(tla.lt(tla.int(0), indexCellBase1asInt).as(BoolT1()),
                  tla.le(indexCellBase1asInt, tla.int(capacity)).as(BoolT1()))
              .as(BoolT1())
          // (indexBase1 - 1 = oracle) <=> inRange
          val oracleEqArg =
            tla
              .eql(tla.minus(indexCellBase1asInt, tla.int(1)).as(IntT1()), oracle.intCell.toNameEx.as(IntT1()))
              .as(IntT1())
              .as(BoolT1())
          val iff = tla.eql(oracleEqArg, inRange).as(BoolT1())
          rewriter.solverContext.assertGroundExpr(iff)
          nextState.setRex(pickedResult.toNameEx)

        case Some(cachedBigInt) =>
          // Special case: the integer is found in the value cache.
          // This can happen if the expression is written under a quantifier over the sequence domain.
          // For instance, \A i \in DOMAIN seq: seq[i] > 0.
          // In this case, we do not have to introduce any constraints!
          if (cachedBigInt < 1 || cachedBigInt > capacity) {
            // Return the default value. We cannot throw an exception, as it may break a valid TLA+ spec.
            nextState.setRex(defaultValue.toNameEx)
          } else {
            // Retrieve the element by its index.
            val elem = elems(state.arena, protoSeq)(cachedBigInt.toInt - 1)
            nextState.setRex(elem.toNameEx)
          }
      }
    }
  }

  /**
   * Make a sequence out of a proto sequence. This method works over symbolic states. If you work over arenas, use
   * [[mkSeqCell]].
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
  def mkSeq(
      state: SymbState,
      seqT: TlaType1,
      protoSeq: ArenaCell,
      len: ArenaCell): SymbState = {
    val (newArena, seqCell) = mkSeqCell(state.arena, seqT, protoSeq, len)
    state.setArena(newArena).setRex(seqCell.toNameEx)
  }

  /**
   * Make a sequence out of a proto sequence. This method works over arenas. Often, it is more convenient to work with
   * [[mkSeq]].
   *
   * @param arena
   *   an arena to start with
   * @param seqT
   *   the type of the sequence
   * @param protoSeq
   *   a proto sequence
   * @param len
   *   a cell that encodes the actual length of the sequence
   * @return
   *   the new symbolic state that contains the created sequence as the expression
   */
  def mkSeqCell(
      arena: Arena,
      seqT: TlaType1,
      protoSeq: ArenaCell,
      len: ArenaCell): (Arena, ArenaCell) = {
    var newArena = arena.appendCell(CellT.fromType1(seqT))
    val seq = newArena.topCell
    // note that we do not track in SMT the relation between the sequence, the proto sequence, and its length
    newArena = newArena.appendHasNoSmt(seq, len, protoSeq)
    (newArena, seq)
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
  def foldLeft(
      picker: CherryPick,
      state: SymbState,
      protoSeq: ArenaCell,
      len: ArenaCell,
      binOp: (SymbState, ArenaCell) => SymbState): SymbState = {
    // propagate the result only if the element is below the length
    def applyOne(state: SymbState, elem: ArenaCell, indexBase1: Int) = {
      // apply the operator, whether we have reached the length or not (we don't know statically)
      var nextState = binOp(state, elem)
      val newResult = nextState.asCell
      // choose between the old result (if above the length) and the new result (if not above the length)
      val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(nextState, 2)
      nextState = picker
        .pickByOracle(oracleState, oracle, Seq(state.asCell, newResult), nextState.arena.cellTrue().toNameEx)
      val picked = nextState.ex
      val inRange = tla.le(tla.int(indexBase1), len.toNameEx.as(IntT1())).as(BoolT1())
      val pickNew = oracle.whenEqualTo(nextState, 1).as(BoolT1())
      val eql = tla.eql(inRange, pickNew).as(BoolT1())
      rewriter.solverContext.assertGroundExpr(eql)

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
