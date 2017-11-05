package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolT, CellT, FinSetT, UnknownT}
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

import scala.collection.immutable.HashMap

object Arena {
  protected val falseName: String = CellTheory().namePrefix + "0"
  protected val trueName: String = CellTheory().namePrefix + "1"
  protected val booleanName: String = CellTheory().namePrefix + "2"

  def create(solverContext: SolverContext): Arena = {
    val arena = new Arena(solverContext, 0,
      new ArenaCell(-1, UnknownT()),
      HashMap(),
      new LazyEquality(solverContext),
      new HashMap(),
      new HashMap()
    ) /////
    // by convention, the first cells have the following semantics: 0 stores FALSE, 1 stores TRUE, 2 stores BOOLEAN
    val newArena = arena.appendCellWithoutDeclaration(BoolT())
      .appendCellWithoutDeclaration(BoolT())
      .appendCellWithoutDeclaration(FinSetT(BoolT()))
    // declare the cells in SMT
    val cellFalse = newArena.cellFalse()
    val cellTrue = newArena.cellTrue()
    val cellBoolean = newArena.cellBoolean()
    solverContext.declareCell(cellFalse)
    solverContext.declareCell(cellTrue)
    solverContext.declareCell(cellBoolean)
    solverContext.assertGroundExpr(OperEx(TlaOper.ne, cellFalse.toNameEx, cellTrue.toNameEx))
    // assert in(c_FALSE, c_BOOLEAN) and in(c_TRUE, c_BOOLEAN)
    solverContext.assertGroundExpr(OperEx(TlaSetOper.in, cellFalse.toNameEx, cellBoolean.toNameEx))
    solverContext.assertGroundExpr(OperEx(TlaSetOper.in, cellTrue.toNameEx, cellBoolean.toNameEx))
    // link c_BOOLEAN to c_FALSE and c_TRUE
    newArena.appendHas(cellBoolean, cellFalse)
      .appendHas(cellBoolean, cellTrue)
  }
}

/**
  * A memory arena represents a memory layout. The arena is dynamically populated, when new objects are created.
  * Currently, an arena is a directed acyclic graph, where edges are pointing from a container object
  * to the associated cells, e.g., a set cell points to the cells that store its elements.
  *
  * @author Igor Konnov
  */
class Arena private(val solverContext: SolverContext,
                    val cellCount: Int, val topCell: ArenaCell,
                    val cellMap: Map[String, ArenaCell],
                    val lazyEquality: LazyEquality,
                    private val hasEdges: Map[ArenaCell, List[ArenaCell]],
                    private val domEdges: Map[ArenaCell, ArenaCell]) {
  // since the edges in arenas have different structure, for the moment, we keep them in different maps
  /*
    private val domEdges: Map[ArenaCell, ArenaCell] = new HashMap[ArenaCell, ArenaCell]
    private val codomEdges: Map[ArenaCell, ArenaCell] = new HashMap[ArenaCell, ArenaCell]
  */

  def cellFalse(): ArenaCell = {
    cellMap(Arena.falseName)
  }

  def cellTrue(): ArenaCell = {
    cellMap(Arena.trueName)
  }

  def cellBoolean(): ArenaCell = {
    cellMap(Arena.booleanName)
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
    * @throws InvalidTlaExException if the name does not follow the convention
    * @throws NoSuchElementException when no cell is found
    */
  def findCellByNameEx(nameEx: TlaEx): ArenaCell = {
    cellMap(CellTheory().nameExToString(nameEx))
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
    cellType match {
      case BoolT() =>
        val cons = OperEx(TlaBoolOper.or, newCell.mkTlaEq(cellFalse()), newCell.mkTlaEq(cellTrue()))
        solverContext.assertGroundExpr(cons)

      case _ =>
        ()
    }
    newArena
  }

  protected def appendCellWithoutDeclaration(cellType: CellT): Arena = {
    val newCell = new ArenaCell(cellCount, cellType)
    new Arena(solverContext, cellCount + 1, newCell,
      cellMap + (newCell.toString -> newCell), lazyEquality, hasEdges, domEdges)
  }

  /**
    * Append a 'has' edge to connect a cell that corresponds to a set with a cell that corresponds to its element.
    *
    * @param setCell  a set cell
    * @param elemCell an element cell
    * @return a new arena
    */
  def appendHas(setCell: ArenaCell, elemCell: ArenaCell): Arena = {
    val es =
      hasEdges.get(setCell) match {
        case Some(list) => list :+ elemCell
        case None => List(elemCell)
      }

    new Arena(solverContext, cellCount, topCell, cellMap, lazyEquality, hasEdges + (setCell -> es), domEdges)
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

    new Arena(solverContext, cellCount, topCell, cellMap, lazyEquality, hasEdges, domEdges + (funCell -> domCell))
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
