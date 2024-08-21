package at.forsyte.apalache.tla.bmcmt.arena

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, ElemPtr, FixedElemPtr, PureArena}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.{tlaU => tla}

/**
 * Declares the same interface as [[Arena]]s (with the exception of [[ElemPtr]] usage).
 *
 * As a transitional step, this class serves to replace [[Arena]]s, but internally separately delegates code to either
 * the context or the arena. In the future, rules will handle context operations and this class will be retired in favor
 * of [[PureArena]]s.
 *
 * @author
 *   Jure Kukovec
 */
case class PureArenaAdapter(arena: PureArena, context: SolverContext) {

  def cellCount: Int = arena.cellCount

  def topCell: ArenaCell = arena.topCell

  def setSolver(newSolverContext: SolverContext): PureArenaAdapter = this.copy(context = newSolverContext)

  /**
   * A fixed cell that equals to false in the Boolean theory.
   *
   * @return
   *   the false cell
   */
  def cellFalse(): ArenaCell = PureArena.cellFalse(arena)

  /**
   * A fixed cell that equals to true in the Boolean theory
   *
   * @return
   *   the true cell
   */
  def cellTrue(): ArenaCell = PureArena.cellTrue(arena)

  /**
   * A fixed cell that stores the set {false, true}, that is, the set BOOLEAN in TLA+.
   *
   * @return
   *   the cell for the BOOLEAN set
   */
  def cellBooleanSet(): ArenaCell = PureArena.cellBooleanSet(arena)

  /**
   * A fixed cell that stores the set Nat. As this set is infinite, it is not pointing to any other cells.
   *
   * @return
   *   the cell for the Nat cell
   */
  def cellNatSet(): ArenaCell = PureArena.cellNatSet(arena)

  /**
   * A fixed cell that stores the set Int. As this set is infinite, it is not pointing to any other cells.
   *
   * @return
   *   the cell for the Int cell
   */
  def cellIntSet(): ArenaCell = PureArena.cellIntSet(arena)

  /**
   * Find a cell by its name.
   *
   * @param name
   *   the name returned by ArenaCell.toString
   * @return
   *   the cell, if it exists
   * @throws java.util.NoSuchElementException
   *   when no cell is found
   */
  def findCellByName(name: String): ArenaCell = arena.findCellByName(name)

  /**
   * Find a cell by the name contained in a name expression.
   *
   * @param nameEx
   *   a name expression that follows the cell naming convention.
   * @return
   *   the found cell
   * @throws InvalidTlaExException
   *   if the name does not follow the convention
   * @throws java.util.NoSuchElementException
   *   when no cell is found
   */
  def findCellByNameEx(nameEx: TlaEx): ArenaCell = arena.findCellByNameEx(nameEx)

  /**
   * Append a new cell to arena. This method returns a new arena, not the new cell. The new cell can be accessed with
   * topCell. This method will be removed, when we fully migrate from {{{CellT}}} to {{{TlaType1}}}.
   *
   * @param cellType
   *   a cell type
   * @param isUnconstrained
   *   a flag defining if the SMT representation of the cell is unconstrained, default is false.
   * @return
   *   new arena
   */
  def appendCellOld(cellType: CellT, isUnconstrained: Boolean = false): PureArenaAdapter = {
    val newArena = appendCellNoSmt(cellType, isUnconstrained)
    val newCell = newArena.topCell
    context.declareCell(newCell)
    newArena
  }

  /**
   * Append a new cell to arena. This method returns a new arena, not the new cell. The new cell can be accessed with
   * topCell.
   *
   * @param cellType
   *   a cell type
   * @param isUnconstrained
   *   a flag defining if the SMT representation of the cell is unconstrained, default is false.
   * @return
   *   new arena
   */
  def appendCell(cellType: TlaType1, isUnconstrained: Boolean = false): PureArenaAdapter =
    appendCellOld(CellT.fromType1(cellType), isUnconstrained)

  /**
   * Append a sequence of cells to arena. This method returns a new arena and a sequence of the freshly created cells
   * (the cells are ordered the same way as the sequence of types). This method provides us with a handy alternative to
   * appendCell, when several cells should be created.
   *
   * @param types
   *   a sequence of cell types
   * @return
   *   a pair: the new arena and a sequence of new cells
   */
  def appendCellSeq(types: CellT*): (PureArenaAdapter, Seq[ArenaCell]) =
    types.foldRight((this, Seq.empty[ArenaCell])) { case (cellT, (a, seq)) =>
      val nextArena = a.appendCellOld(cellT)
      val nextCell = nextArena.topCell
      (nextArena, nextCell +: seq)
    }

  /**
   * Append a new cell to arena. This method returns a new arena, not the new cell. The new cell can be accessed with
   * topCell. This method does not generate SMT constraints.
   *
   * @param cellType
   *   a cell type
   * @param isUnconstrained
   *   a flag defining if the SMT representation of the cell is unconstrained, default is false.
   * @return
   *   new arena
   */
  def appendCellNoSmt(cellType: CellT, isUnconstrained: Boolean = false): PureArenaAdapter = {
    val newCell = arena.nextCell(cellType, isUnconstrained)
    assert(!arena.cellMap.contains(newCell.toString)) // this might happen, if we messed up arenas
    this.copy(arena = arena.appendCell(newCell))
  }

  /**
   * Append 'has' edges that connect the first cell to the other cells, in the given order. The previously added edges
   * come first. When this method is called as appendHas(X, Y1, ..., Ym), it adds a Boolean constant in_X_Yi for each i:
   * 1 <= i <= m.
   *
   * @param parentCell
   *   the cell that points to the children cells
   * @param childrenCells
   *   the cells that are pointed by the parent cell
   * @return
   *   the updated arena
   */
  def appendHas(parentCell: ArenaCell, childrenCells: ElemPtr*): PureArenaAdapter =
    childrenCells.foldLeft(this) { (a, c) =>
      a.appendOneHasEdge(addInPred = true, parentCell, c)
    }

  /**
   * Append 'has' edges that connect the first cell to the other cells, in the given order. The previously added edges
   * come first. In contrast to appendHas, this method does not add any constants in SMT.
   *
   * @param parentCell
   *   the cell that points to the children cells
   * @param childrenCells
   *   the cells that are pointed by the parent cell
   * @return
   *   the updated arena
   */
  def appendHasNoSmt(parentCell: ArenaCell, childrenCells: ElemPtr*): PureArenaAdapter =
    this.copy(arena = arena.appendHas(parentCell, childrenCells: _*))

  /**
   * Append a 'has' edge to connect a cell that corresponds to a set with a cell that corresponds to its element.
   *
   * @param setCell
   *   a set cell
   * @param elemCell
   *   an element cell
   * @param addInPred
   *   indicates whether the in_X_Y constant should be added in SMT.
   * @return
   *   a new arena
   */
  private def appendOneHasEdge(
      addInPred: Boolean,
      setCell: ArenaCell,
      elemCell: ElemPtr): PureArenaAdapter = {
    if (addInPred) {
      context.declareInPredIfNeeded(setCell, elemCell.elem)
    }
    appendHasNoSmt(setCell, elemCell)
  }

  /**
   * Get all the edges that are labelled with 'has'.
   *
   * @param setCell
   *   a set cell
   * @return
   *   all element cells that were added with appendHas, or an empty list, if none were added
   */
  def getHas(setCell: ArenaCell): Seq[ArenaCell] =
    // TODO: temporarily return cells not pointers, while we implement pointer support. Use getHasPtr for chaining.
    arena.getHas(setCell).map(_.elem)

  def getHasPtr(setCell: ArenaCell): Seq[ElemPtr] = arena.getHas(setCell)

  /**
   * Set a function domain.
   *
   * @param funCell
   *   a function cell.
   * @param domCell
   *   a set cell
   * @return
   *   a new arena
   */
  def setDom(funCell: ArenaCell, domCell: ArenaCell): PureArenaAdapter = {
    if (arena.hasDom(funCell))
      throw new IllegalStateException("Trying to set function domain, whereas one is already set")

    this.copy(arena = arena.setDom(funCell, domCell))
  }

  /**
   * Set a function co-domain.
   *
   * @param funCell
   *   a function cell.
   * @param cdmCell
   *   a set cell
   * @return
   *   a new arena
   */
  def setCdm(funCell: ArenaCell, cdmCell: ArenaCell): PureArenaAdapter = {
    if (arena.hasCdm(funCell))
      throw new IllegalStateException("Trying to set function co-domain, whereas one is already set")

    this.copy(arena = arena.setCdm(funCell, cdmCell))
  }

  /**
   * Get the domain cell associated with a function.
   *
   * @param funCell
   *   a function cell.
   * @return
   *   the domain cell
   */
  def getDom(funCell: ArenaCell): ArenaCell = arena.getDom(funCell)

  /**
   * Get the co-domain cell associated with a function.
   *
   * @param funCell
   *   a function cell.
   * @return
   *   the co-domain cell
   */
  def getCdm(funCell: ArenaCell): ArenaCell = arena.getCdm(funCell)

  /**
   * Check, whether a cell has an associated domain edge.
   *
   * @param cell
   *   a cell
   * @return
   *   true, if cell has an edge labelled with 'dom'
   */
  def hasDom(cell: ArenaCell): Boolean = arena.hasDom(cell)

  /**
   * Check, whether a cell has an associated co-domain edge.
   *
   * @param cell
   *   a cell
   * @return
   *   true, if cell has an edge labelled with 'cdm'
   */
  def hasCdm(cell: ArenaCell): Boolean = arena.hasCdm(cell)

  /**
   * Check, whether two cells are connected with a 'has' edge.
   *
   * @param src
   *   an edge origin
   * @param dst
   *   an edge destination
   * @return
   *   true, if src has an edge to dst labelled with 'has'
   */
  def isLinkedViaHas(src: ArenaCell, dst: ArenaCell): Boolean = arena.isLinkedViaHas(src, dst)

  /**
   * Find all the cells of a given type.
   *
   * @return
   *   all the cells that have exactly the same type as the argument (no unification involved)
   */
  def findCellsByType(cellType: CellT): Seq[ArenaCell] = arena.findCellsByType(cellType)

  /**
   * Print the graph structure induced by 'has' edges starting with root.
   *
   * @param root
   *   a cell to start from
   */
  def subgraphToString(root: ArenaCell): String = {
    val builder = new StringBuilder()

    def print(cell: ArenaCell): Unit = {
      builder.append(cell.id)
      builder.append(" ")
      val cells = getHas(cell)
      if (cells.nonEmpty) {
        builder.append("has:(")
        for (c <- cells)
          print(c)
        builder.append(")")
      }
    }

    print(root)
    builder.mkString
  }

}

object PureArenaAdapter {
  def create(solverContext: SolverContext): PureArenaAdapter = {
    val emptyArena = PureArena.empty
    // by convention, the first cells have the following semantics:
    //  0 stores FALSE, 1 stores TRUE, 2 stores BOOLEAN, 3 stores Nat, 4 stores Int
    val appendSeq = Seq(
        CellTFrom(BoolT1),
        CellTFrom(BoolT1),
        CellTFrom(SetT1(BoolT1)),
        InfSetT(CellTFrom(IntT1)),
        InfSetT(CellTFrom(IntT1)),
    )

    val (initArena, cells) = emptyArena.appendCellSeq(appendSeq: _*)
    // declare Boolean cells in SMT
    val Seq(cellFalse, cellTrue, cellBoolean, _, _) = cells
    cells.foreach(solverContext.declareCell)

    solverContext.assertGroundExpr(tla.not(cellFalse.toBuilder))
    solverContext.assertGroundExpr(cellTrue.toBuilder)
    // link c_BOOLEAN to c_FALSE and c_TRUE
    val ret = PureArenaAdapter(initArena, solverContext)
      .appendHas(cellBoolean, Seq(cellFalse, cellTrue).map(FixedElemPtr): _*)
    // assert in(c_FALSE, c_BOOLEAN) and in(c_TRUE, c_BOOLEAN)
    ret.context.assertGroundExpr(tla.storeInSet(cellFalse.toBuilder, cellBoolean.toBuilder))
    ret.context.assertGroundExpr(tla.storeInSet(cellTrue.toBuilder, cellBoolean.toBuilder))
    ret
  }
}
