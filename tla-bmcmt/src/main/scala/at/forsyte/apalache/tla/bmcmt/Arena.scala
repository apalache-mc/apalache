package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

import scala.collection.immutable.HashMap

object Arena {
  /**
    * The prefix of all cells.
    */
  val namePrefix = "$C$"

  val falseName: String = namePrefix + "0"
  val trueName: String = namePrefix + "1"
  val booleanSetName: String = namePrefix + "2"
  val natSetName: String = namePrefix + "3"
  val intSetName: String = namePrefix + "4"

  def create(solverContext: SolverContext): Arena = {
    var arena = new Arena(solverContext, 0,
      new ArenaCell(-1, UnknownT()),
      HashMap(),
      new HashMap(),
      new HashMap(),
      new HashMap()
    ) /////
    // by convention, the first cells have the following semantics:
    //  0 stores FALSE, 1 stores TRUE, 2 stores BOOLEAN, 3 stores Nat, 4 stores Int
    arena = arena.appendCellWithoutDeclaration(BoolT())
      .appendCellWithoutDeclaration(BoolT())
      .appendCellWithoutDeclaration(FinSetT(BoolT()))
      .appendCellWithoutDeclaration(InfSetT(IntT()))
      .appendCellWithoutDeclaration(InfSetT(IntT()))
    // declare Boolean cells in SMT
    val cellFalse = arena.cellFalse()
    val cellTrue = arena.cellTrue()
    val cellBoolean = arena.cellBooleanSet()
    val cellNat = arena.cellNatSet()
    val cellInt = arena.cellIntSet()
    solverContext.declareCell(cellFalse)
    solverContext.declareCell(cellTrue)
    solverContext.declareCell(cellBoolean)
    solverContext.declareCell(cellNat)
    solverContext.declareCell(cellInt)
    solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, cellFalse.toNameEx))
    solverContext.assertGroundExpr(cellTrue.toNameEx)
    // link c_BOOLEAN to c_FALSE and c_TRUE
    arena = arena.appendHas(cellBoolean, cellFalse).appendHas(cellBoolean, cellTrue)
    // assert in(c_FALSE, c_BOOLEAN) and in(c_TRUE, c_BOOLEAN)
    solverContext.assertGroundExpr(OperEx(TlaSetOper.in, cellFalse.toNameEx, cellBoolean.toNameEx))
    solverContext.assertGroundExpr(OperEx(TlaSetOper.in, cellTrue.toNameEx, cellBoolean.toNameEx))
    arena
  }
}

/**
  * <p>A memory arena represents a memory layout. The arena is dynamically populated, when new objects are created.
  * Currently, an arena is a directed acyclic graph, where edges are pointing from a container object
  * to the associated cells, e.g., a set cell points to the cells that store its elements.</p>
  *
  * <p>Do not use solverContext, as it is going to be removed in the future.</p>
  *
  * @author Igor Konnov
  */
class Arena private(val solverContext: SolverContext,
                    val cellCount: Int,
                    val topCell: ArenaCell,
                    val cellMap: Map[String, ArenaCell],
                    private val hasEdges: Map[ArenaCell, List[ArenaCell]],
                    private val domEdges: Map[ArenaCell, ArenaCell],
                    private val cdmEdges: Map[ArenaCell, ArenaCell]) extends Serializable {
  // TODO: remove solverContext from Arena!
  def setSolver(newSolverContext: SolverContext): Arena = {
    // this is a temporary solution
    new Arena(newSolverContext, cellCount, topCell, cellMap, hasEdges, domEdges, cdmEdges)
  }

  /**
    * A fixed cell that equals to false in the Boolean theory.
    * @return the false cell
    */
  def cellFalse(): ArenaCell = {
    cellMap(Arena.falseName)
  }

  /**
    * A fixed cell that equals to true in the Boolean theory
    * @return the true cell
    */
  def cellTrue(): ArenaCell = {
    cellMap(Arena.trueName)
  }

  /**
    * A fixed cell that stores the set {false, true}, that is, the set BOOLEAN in TLA+.
    * @return the cell for the BOOLEAN set
    */
  def cellBooleanSet(): ArenaCell = {
    cellMap(Arena.booleanSetName)
  }

  /**
    * A fixed cell that stores the set Nat. As this set is infinite, it is not pointing to any other cells.
    * @return the cell for the Nat cell
    */
  def cellNatSet(): ArenaCell = {
    cellMap(Arena.natSetName)
  }

  /**
    * A fixed cell that stores the set Int. As this set is infinite, it is not pointing to any other cells.
    * @return the cell for the Int cell
    */
  def cellIntSet(): ArenaCell = {
    cellMap(Arena.intSetName)
  }

  /**
    * Find a cell by its name.
    *
    * @param name the name returned by ArenaCell.toString
    * @return the cell, if it exists
    * @throws NoSuchElementException when no cell is found
    */
  def findCellByName(name: String): ArenaCell = {
    cellMap(name)
  }

  /**
    * Find a cell by the name contained in a name expression.
    *
    * @param nameEx a name expression that follows the cell naming convention.
    * @return the found cell
    * @throws InvalidTlaExException  if the name does not follow the convention
    * @throws NoSuchElementException when no cell is found
    */
  def findCellByNameEx(nameEx: TlaEx): ArenaCell = {
    nameEx match {
      case NameEx(name) if ArenaCell.isValidName(name) =>
        cellMap(name)

      case _ =>
        throw new CheckerException("Expected NameEx with a cell name, found: %s".format(nameEx), nameEx)
    }

  }

  /**
    * Append a new cell to arena. This method returns a new arena, not the new cell.
    * The new cell can be accessed with topCell.
    *
    * @param cellType a cell type
    * @return new arena
    */
  def appendCell(cellType: CellT): Arena = {
    val newArena = appendCellWithoutDeclaration(cellType)
    val newCell = newArena.topCell
    solverContext.declareCell(newCell)
    newArena
  }

  /**
    * Append a sequence of cells to arena. This method returns a new arena and a sequence of the freshly
    * created cells (the cells are ordered the same way as the sequence of types). This method provides us with a
    * handy alternative to appendCell, when several cells should be created.
    * @param types a sequence of cell types
    * @return a pair: the new arena and a sequence of new cells
    */
  def appendCellSeq(types: CellT*): (Arena, Seq[ArenaCell]) = {
    def create(arena: Arena, ts: Seq[CellT]): (Arena, Seq[ArenaCell]) =
      ts match {
        case Seq() =>
          (arena, Seq())

        case hd +: tl =>
          val (tailArena: Arena, tailCells: Seq[ArenaCell]) = create(arena, tl)
          val headArena = tailArena.appendCell(hd)
          (headArena, headArena.topCell +: tailCells)
      }

    create(this, types)
  }

  protected def appendCellWithoutDeclaration(cellType: CellT): Arena = {
    val newCell = new ArenaCell(cellCount, cellType)
    assert(!cellMap.contains(newCell.toString)) // this might happen, if we messed up arenas
    new Arena(solverContext, cellCount + 1, newCell,
      cellMap + (newCell.toString -> newCell), hasEdges, domEdges, cdmEdges)
  }

  /**
    * Append 'has' edges that connect the first cell to the other cells, in the given order.
    * The previously added edges come first. When this method is called as appendHas(X, Y1, ..., Ym),
    * it adds a Boolean constant in_X_Yi for each i: 1 <= i <= m.
    *
    * @param parentCell the cell that points to the children cells
    * @param childrenCells the cells that are pointed by the parent cell
    * @return the updated arena
    */
  def appendHas(parentCell: ArenaCell, childrenCells: ArenaCell*): Arena = {
    childrenCells.foldLeft(this) { (a, c) => a.appendOneHasEdge(addInPred = true, parentCell, c) }
  }

  /**
    * Append 'has' edges that connect the first cell to the other cells, in the given order.
    * The previously added edges come first. In contrast to appendHas, this method does not add any constants in SMT.
    *
    * @param parentCell the cell that points to the children cells
    * @param childrenCells the cells that are pointed by the parent cell
    * @return the updated arena
    */
  def appendHasNoSmt(parentCell: ArenaCell, childrenCells: ArenaCell*): Arena = {
    childrenCells.foldLeft(this) { (a, c) => a.appendOneHasEdge(addInPred = false, parentCell, c) }
  }

  /**
    * Append a 'has' edge to connect a cell that corresponds to a set with a cell that corresponds to its element.
    *
    * @param setCell  a set cell
    * @param elemCell an element cell
    * @param addInPred indicates whether the in_X_Y constant should be added in SMT.
    * @return a new arena
    */
  private def appendOneHasEdge(addInPred: Boolean, setCell: ArenaCell, elemCell: ArenaCell): Arena = {
    if (addInPred) {
      solverContext.declareInPredIfNeeded(setCell, elemCell)
    }
    val es =
      hasEdges.get(setCell) match {
        case Some(list) =>
          list :+ elemCell

        case None =>
          List(elemCell)
      }

    new Arena(solverContext, cellCount, topCell, cellMap, hasEdges + (setCell -> es), domEdges, cdmEdges)
  }

  /**
    * Get all the edges that are labelled with 'has'.
    *
    * @param setCell a set cell
    * @return all element cells that were added with appendHas, or an empty list, if none were added
    */
  def getHas(setCell: ArenaCell): List[ArenaCell] = {
    hasEdges.get(setCell) match {
      case Some(list) => list
      case None => List()
    }
  }

  /**
    * Set a function domain.
    *
    * @param funCell a function cell.
    * @param domCell a set cell
    * @return a new arena
    */
  def setDom(funCell: ArenaCell, domCell: ArenaCell): Arena = {
    if (domEdges.contains(funCell))
      throw new IllegalStateException("Trying to set function domain, whereas one is already set")

    new Arena(solverContext,
      cellCount, topCell, cellMap, hasEdges, domEdges + (funCell -> domCell), cdmEdges)
  }

  /**
    * Set a function co-domain.
    *
    * @param funCell a function cell.
    * @param cdmCell a set cell
    * @return a new arena
    */
  def setCdm(funCell: ArenaCell, cdmCell: ArenaCell): Arena = {
    if (cdmEdges.contains(funCell))
      throw new IllegalStateException("Trying to set function co-domain, whereas one is already set")

    new Arena(solverContext,
      cellCount, topCell, cellMap, hasEdges, domEdges, cdmEdges + (funCell -> cdmCell))
  }

  /**
    * Get the domain cell associated with a function.
    *
    * @param funCell a function cell.
    * @return the domain cell
    */
  def getDom(funCell: ArenaCell): ArenaCell = {
    domEdges.apply(funCell)
  }

  /**
    * Get the co-domain cell associated with a function.
    *
    * @param funCell a function cell.
    * @return the co-domain cell
    */
  def getCdm(funCell: ArenaCell): ArenaCell = {
    cdmEdges.apply(funCell)
  }

  /**
    * Check, whether a cell has an associated domain edge.
    *
    * @param cell a cell
    * @return true, if cell has an edge labelled with 'dom'
    */
  def hasDom(cell: ArenaCell): Boolean = {
    domEdges.contains(cell)
  }

  /**
    * Check, whether a cell has an associated co-domain edge.
    *
    * @param cell a cell
    * @return true, if cell has an edge labelled with 'cdm'
    */
  def hasCdm(cell: ArenaCell): Boolean = {
    cdmEdges.contains(cell)
  }

  /**
    * Check, whether two cells are connected with a 'has' edge.
    *
    * @param src an edge origin
    * @param dst an edge destination
    * @return true, if src has an edge to dst labelled with 'has'
    */
  def isLinkedViaHas(src: ArenaCell, dst: ArenaCell): Boolean = {
    def default(c: ArenaCell): List[ArenaCell] = List()

    hasEdges.applyOrElse(src, default).contains(dst)
  }

  /**
    * Find all the cells of a given type.
    *
    * @return all the cells that have exactly the same type as the argument (no unification involved)
    */
  def findCellsByType(cellType: CellT): List[ArenaCell] = {
    cellMap.values.filter(_.cellType == cellType).toList
  }

  /**
    * Print the graph structure induced by 'has' edges starting with root.
    *
    * @param root a cell to start from
    */
  def subgraphToString(root: ArenaCell): String = {
    val builder = StringBuilder.newBuilder

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
