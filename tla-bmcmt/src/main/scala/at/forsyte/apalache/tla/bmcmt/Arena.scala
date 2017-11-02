package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolType, CellType, FinSetType, UnknownType}
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}

import scala.collection.immutable.HashMap

object Arena {
  protected val falseName: String = ArenaCell.namePrefix + "0"
  protected val trueName: String = ArenaCell.namePrefix + "1"
  protected val booleanName: String = ArenaCell.namePrefix + "2"

  def create(solverContext: SolverContext): Arena = {
    val arena = new Arena(solverContext, 0, new ArenaCell(-1, UnknownType()), HashMap(), new HashMap())
    // by convention, the first cells have the following semantics: 0 stores FALSE, 1 stores TRUE, 2 stores BOOLEAN
    val newArena = arena.appendCellWithoutDeclaration(BoolType())
      .appendCellWithoutDeclaration(BoolType())
      .appendCellWithoutDeclaration(FinSetType(BoolType()))
    // declare the cells in SMT
    solverContext.declareCell(newArena.cellFalse())
    solverContext.declareCell(newArena.cellTrue())
    solverContext.declareCell(newArena.cellBoolean())
    solverContext.assertCellExpr(OperEx(TlaOper.ne, newArena.cellFalse().toNameEx, newArena.cellTrue().toNameEx))
    // link c_BOOLEAN to c_FALSE and c_TRUE
    newArena.appendHas(newArena.cellBoolean(), newArena.cellFalse())
        .appendHas(newArena.cellBoolean(), newArena.cellTrue())
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
                    private val hasEdges: Map[ArenaCell, List[ArenaCell]]) {
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
    */
  def findCellByName(name: String): ArenaCell = {
    cellMap(name)
  }

  /**
    * Append a new cell to arena. This method returns a new arena, not the new cell.
    * The new cell can be accessed with topCell.
    *
    * @param cellType a cell type
    * @return new arena
    */
  def appendCell(cellType: CellType): Arena = {
    val newArena = appendCellWithoutDeclaration(cellType)
    val newCell = newArena.topCell
    solverContext.declareCell(newCell)
    cellType match {
      case BoolType() =>
        val cons = OperEx(TlaBoolOper.or, newCell.mkTlaEq(cellFalse()), newCell.mkTlaEq(cellTrue()))
        solverContext.assertCellExpr(cons)

      case _ =>
        ()
    }
    newArena
  }

  protected def appendCellWithoutDeclaration(cellType: CellType): Arena = {
    val newCell = new ArenaCell(cellCount, cellType)
    new Arena(solverContext, cellCount + 1, newCell, cellMap + (newCell.toString -> newCell), hasEdges)
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

    new Arena(solverContext, cellCount, topCell, cellMap, hasEdges + (setCell -> es))
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
}
