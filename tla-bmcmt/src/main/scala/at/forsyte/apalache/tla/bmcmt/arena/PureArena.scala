package at.forsyte.apalache.tla.bmcmt.arena

import at.forsyte.apalache.tla.bmcmt.types.{CellT, UnknownT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, CheckerException}
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}

/**
 * An SMT-context free implementation of arenas.
 *
 * @author
 *   Jure Kukovec
 */
case class PureArena(
    cellMap: Map[String, ArenaCell],
    private val hasEdges: Map[ArenaCell, Seq[ElemPtr]],
    private val domEdges: Map[ArenaCell, ArenaCell],
    private val cdmEdges: Map[ArenaCell, ArenaCell],
    // The next two are caches
    topCell: ArenaCell = PureArena.cellInvalid,
    cellCount: Int = 0) {

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
  def findCellByName(name: String): ArenaCell = cellMap(name)

  /**
   * Find a cell by the name contained in a name expression.
   *
   * @param nameEx
   *   a name expression that follows the cell naming convention.
   * @return
   *   the found cell
   * @throws CheckerException
   *   if the name does not follow the convention
   * @throws java.util.NoSuchElementException
   *   when no cell is found
   */
  def findCellByNameEx(nameEx: TlaEx): ArenaCell = nameEx match {
    // is the _if_ necessary? If the name is invalid, we'll hit an "element not found" exception anyway
    case NameEx(name) if ArenaCell.isValidName(name) => findCellByName(name)
    case _ => throw new CheckerException("Expected NameEx with a cell name, found: %s".format(nameEx), nameEx)
  }

  /**
   * Append a new cell to arena. This method returns a new arena. The new cell can be accessed with topCell.
   *
   * @param cell
   *   the cell to append
   * @return
   *   new arena
   */
  def appendCell(cell: ArenaCell): PureArena = {
    if (cellMap.contains(cell.toString))
      throw new Exception(s"Cell $cell is already a member of the arena.")
    this.copy(cellMap = cellMap + (cell.toString -> cell), topCell = cell, cellCount = cellCount + 1)
  }

  /**
   * Alternative to [[appendCell]], where the appended cell is freshly created by [[nextCell]] and may be accessed by
   * [[topCell]] afterwards.
   *
   * @param cellType
   *   the cell type of the newly appended cell
   * @return
   *   new arena
   */
  def appendCell(cellT: CellT): PureArena = appendCell(nextCell(cellT))

  /**
   * @see
   *   [[appendCell]]
   */
  def +(cell: ArenaCell): PureArena = appendCell(cell)

  /**
   * Append a sequence of cells to arena. This method returns a new arena. This method provides us with a handy
   * alternative to appendCell, when several cells should be created.
   *
   * @param types
   *   a sequence of cell types
   * @return
   *   the new arena
   */
  def appendCellSeq(cells: ArenaCell*): PureArena = {
    // Fold instead of single-add, so topCell/cellCount gets auto-updated
    cells.foldLeft(this) { case (arena, cell) =>
      arena.appendCell(cell)
    }
  }

  /**
   * Append 'has' edges that connect the first cell to the other cells, in the given order. The previously added edges
   * come first.
   *
   * @param parentCell
   *   the cell that points to the children cells
   * @param childrenCells
   *   the pointers to cells that are pointed by the parent cell
   * @return
   *   the updated arena
   */
  def appendHas(parent: ArenaCell, childrenPtrs: ElemPtr*): PureArena =
    this.copy(hasEdges = hasEdges + (parent -> childrenPtrs))

  /**
   * Get all the edges that are labelled with 'has'.
   *
   * @param setCell
   *   a set cell
   * @return
   *   all element cells that were added with appendHas, or an empty list, if none were added
   */
  def getHas(setCell: ArenaCell): Seq[ElemPtr] = hasEdges.getOrElse(setCell, Seq.empty)

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
  def isLinkedViaHas(src: ArenaCell, dst: ArenaCell): Boolean = getHas(src).exists(_.elem == dst)

  /**
   * Find all the cells of a given type.
   *
   * @return
   *   all the cells that have exactly the same type as the argument (no unification involved)
   */
  def findCellsByType(cellType: CellT): Seq[ArenaCell] =
    cellMap.values.toSeq.filter(_.cellType == cellType)

  /**
   * Check, whether a cell has an associated domain edge.
   *
   * @param cell
   *   a cell
   * @return
   *   true, if cell has an edge labelled with 'dom'
   */
  def hasDom(cell: ArenaCell): Boolean = domEdges.contains(cell)

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
  def setDom(funCell: ArenaCell, domCell: ArenaCell): PureArena =
    this.copy(domEdges = domEdges + (funCell -> domCell))

  /**
   * Get the domain cell associated with a function.
   *
   * @param funCell
   *   a function cell.
   * @return
   *   the domain cell
   */
  def getDom(funCell: ArenaCell): ArenaCell = domEdges(funCell)

  /**
   * Check, whether a cell has an associated co-domain edge.
   *
   * @param cell
   *   a cell
   * @return
   *   true, if cell has an edge labelled with 'cdm'
   */
  def hasCdm(cell: ArenaCell): Boolean = cdmEdges.contains(cell)

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
  def setCdm(funCell: ArenaCell, cdmCell: ArenaCell): PureArena =
    this.copy(domEdges = domEdges + (funCell -> cdmCell))

  /**
   * Get the co-domain cell associated with a function.
   *
   * @param funCell
   *   a function cell.
   * @return
   *   the co-domain cell
   */
  def getCdm(funCell: ArenaCell): ArenaCell = cdmEdges(funCell)

  /**
   * Creates a cell with a unique identifier w.r.t. this arena, assuming all current cell identifiers belong to the
   * range 0..(cellCount-1).
   *
   * @param t
   *   cell type
   * @param isUnconstrained
   *   cell constraint flag
   * @return
   */
  def nextCell(t: CellT, isUnconstrained: Boolean = false): ArenaCell = new ArenaCell(cellCount, t, isUnconstrained)

}

object PureArena {

  import at.forsyte.apalache.tla.bmcmt.Arena.namePrefix

  val falseName: String = namePrefix + "0"
  val trueName: String = namePrefix + "1"
  val booleanSetName: String = namePrefix + "2"
  val natSetName: String = namePrefix + "3"
  val intSetName: String = namePrefix + "4"

  def empty: PureArena = PureArena(Map.empty, Map.empty, Map.empty, Map.empty)

  def cellInvalid: ArenaCell = new ArenaCell(-1, UnknownT())

  def cellFalse(a: PureArena): ArenaCell = a.findCellByName(falseName)

  def cellTrue(a: PureArena): ArenaCell = a.findCellByName(trueName)

  def cellBooleanSet(a: PureArena): ArenaCell = a.findCellByName(booleanSetName)

  def cellNatSet(a: PureArena): ArenaCell = a.findCellByName(natSetName)

  def cellIntSet(a: PureArena): ArenaCell = a.findCellByName(intSetName)

}
