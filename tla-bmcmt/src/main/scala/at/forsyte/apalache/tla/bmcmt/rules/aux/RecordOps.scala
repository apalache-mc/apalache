package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.CellTFrom
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.{RecRowT1, RowT1, TlaType1}

import scala.collection.immutable.SortedMap

/**
 * <p>A small collection of operations on records. We isolate these operations in a single class to re-use them for
 * records and variants. Importantly, this class itself does not use rewriting rules.</p>
 *
 * @param rewriter
 *   state rewriter
 * @author
 *   Igor Konnov
 */
class RecordOps(rewriter: SymbStateRewriter) {

  /**
   * Construct a record.
   *
   * @param state
   *   a symbolic state to start with
   * @param fields
   *   a map from field names to cells
   * @return
   *   a new symbolic state that contains the constructed record (a cell) as an expression
   */
  def make(state: SymbState, fields: SortedMap[String, ArenaCell]): SymbState = {
    // create a record cell
    val recordT = RecRowT1(RowT1(fields.map { case (name, cell) => (name, cell.cellType.toTlaType1) }, None))
    var nextState = state.updateArena(_.appendCell(recordT))
    val recordCell = nextState.arena.topCell
    // add the fields in the order of their names
    for (fieldCell <- fields.valuesIterator) {
      nextState = nextState.updateArena(_.appendHasNoSmt(recordCell, fieldCell))
    }

    // In contrast to the old records, we do not associate the record domain with a record.
    // The record domain can be easily constructed from its type, whenever it is needed (which is rare).

    nextState.setRex(recordCell.toNameEx)
  }

  /**
   * Return the record domain.
   *
   * @param state
   *   a symbolic state to start with
   * @param recordCell
   *   a record cell
   * @return
   *   a new symbolic state that contains the constructed domain
   */
  def domain(state: SymbState, recordCell: ArenaCell): SymbState = {
    val fieldTypes = getFieldTypes(recordCell)
    val fieldNames = fieldTypes.keySet

    val (newArena, domain) = rewriter.recordDomainCache.getOrCreate(state.arena, (fieldNames, fieldNames))
    state.setArena(newArena).setRex(domain.toNameEx)
  }

  /**
   * Get the value of a field by its name.
   *
   * @param arena
   *   current arena
   * @param recordCell
   *   a record cell
   * @param fieldName
   *   a field name
   * @return
   *   a cell that contains the extracted field
   */
  def getField(arena: Arena, recordCell: ArenaCell, fieldName: String): ArenaCell = {
    val fieldTypes = getFieldTypes(recordCell)
    expectFieldName(recordCell, fieldTypes, fieldName)

    val index = fieldTypes.keySet.toList.indexOf(fieldName)
    val elems = arena.getHas(recordCell)
    assert(0 <= index && index < elems.length)
    elems(index)
  }

  /**
   * Update a record field.
   *
   * @param state
   *   a symbolic state to start with
   * @param recordCell
   *   a record cell
   * @param fieldName
   *   the field name to update
   * @param newCell
   *   the new value
   * @return
   *   a new symbolic state that contains the updated record
   */
  def updateField(
      state: SymbState,
      recordCell: ArenaCell,
      fieldName: String,
      newCell: ArenaCell): SymbState = {
    val fieldTypes = getFieldTypes(recordCell)
    expectFieldName(recordCell, fieldTypes, fieldName)
    val index = fieldTypes.keySet.toList.indexOf(fieldName)
    val elems = state.arena.getHas(recordCell)
    assert(0 <= index && index < elems.length)

    var nextState = state.updateArena(_.appendCell(recordCell.cellType.toTlaType1))
    val newRecord = nextState.arena.topCell
    // add the fields in the order of their names, update by name
    for ((name, oldCell) <- fieldTypes.keySet.zip(elems)) {
      val updatedCell = if (name == fieldName) newCell else oldCell
      nextState = nextState.updateArena(_.appendHasNoSmt(newRecord, updatedCell))
    }

    nextState.setRex(newRecord.toNameEx)
  }

  private def expectFieldName(
      recordCell: ArenaCell,
      fieldTypes: SortedMap[String, TlaType1],
      fieldName: String): Unit = {
    if (!fieldTypes.contains(fieldName)) {
      val recordT = RecRowT1(RowT1(fieldTypes, None))
      val msg = s"Accessing a non-existing field $fieldName of record of type $recordT"
      throw new RewriterException(msg, recordCell.toNameEx)
    }
  }

  private def getFieldTypes(cell: ArenaCell): SortedMap[String, TlaType1] = {
    cell.cellType match {
      case CellTFrom(RecRowT1(RowT1(ft, None))) => ft

      case tt =>
        throw new RewriterException(s"Unexpected record type $tt of cell ${cell.id}", cell.toNameEx)
    }
  }
}
