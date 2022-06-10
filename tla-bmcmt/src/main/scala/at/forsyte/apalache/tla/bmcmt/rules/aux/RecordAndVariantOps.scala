package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.CellTFrom
import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.SortedMap

/**
 * <p>A small collection of operations on records and variants. We isolate these operations in a single class to re-use
 * them for records and variants. Importantly, this class itself does not use rewriting rules.</p>
 *
 * @param rewriter
 *   state rewriter
 * @author
 *   Igor Konnov
 */
class RecordAndVariantOps(rewriter: SymbStateRewriter) {
  // the name of the hidden tag field that is attached to every variant
  private val tagField = "__tag"
  // the uninterpreted sort to use for storing the tag values
  private val tagSort = "__TAG"
  private val defaultValueFactory = new DefaultValueFactory(rewriter)

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
  def makeRecord(state: SymbState, fields: SortedMap[String, ArenaCell]): SymbState = {
    // create a record cell
    val recordT = RecRowT1(RowT1(fields.map { case (name, cell) => (name, cell.cellType.toTlaType1) }, None))
    makeRecordInternal(state, fields, recordT)
  }

  // an internal implementation of makeRecord that allows us to associate a target type with the record
  private def makeRecordInternal(
      state: SymbState,
      fields: SortedMap[String, ArenaCell],
      targetType: TlaType1): SymbState = {
    // create a record cell
    var nextState = state.updateArena(_.appendCell(targetType))
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
   * Get or create the arena cell that is associated with a tag name.
   *
   * @param state
   *   a symbolic state
   * @param tagName
   *   the tag name
   * @return
   *   a new symbolic state that contains the constructed tag cell as an expression
   */
  def getOrCreateVariantTag(state: SymbState, tagName: String): SymbState = {
    val (newArena, tagAsCell) = rewriter.modelValueCache.getOrCreate(state.arena, (tagSort, tagName))
    state.setArena(newArena).setRex(tagAsCell.toNameEx)
  }

  /**
   * Construct a variant.
   *
   * @param state
   *   a symbolic state to start with
   * @param variantT
   *   the type of the variant
   * @param tagName
   *   the name of the tag
   * @param value
   *   the value to attach associate with the tag
   * @return
   *   a new symbolic state that contains the constructed record (a cell) as an expression
   */
  def makeVariant(
      state: SymbState,
      variantT: TlaType1,
      tagName: String,
      value: ArenaCell): SymbState = {
    var nextState = state
    variantT match {
      case VariantT1(RowT1(variantOptions, None)) =>
        // create a record that has a value attached to every tag
        val fields = variantOptions.map { case (t, tp) =>
          if (t == tagName) {
            (t, value)
          } else {
            val (newArena, defaultValue) = defaultValueFactory.makeUpValue(nextState.arena, tp)
            nextState = nextState.setArena(newArena)
            (t, defaultValue)
          }
        }

        // add the additional field __tag that stores the tag value
        nextState = getOrCreateVariantTag(nextState, tagName)
        val tagAsCell = nextState.asCell
        // create a record that contains exactly the fields and associate the variant type with it
        makeRecordInternal(nextState, fields + (tagField -> tagAsCell), variantT)

      case _ =>
        throw new TypingException("Unexpected type in Variant: " + variantT, state.ex.ID)
    }
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
   * Get the variant value by tag. This is an unsafe method, that is, if the associated tag name is different from the
   * provided one, this method returns some of the proper type (usually, the default value).
   *
   * @param arena
   *   current arena
   * @param variantCell
   *   a variant cell
   * @param tagName
   *   a field name
   * @return
   *   a cell that contains the extracted field
   */
  def getUnsafeVariantValue(arena: Arena, variantCell: ArenaCell, tagName: String): ArenaCell = {
    val options = getVariantOptions(variantCell)
    expectVariantTag(variantCell, options, tagName)

    val index = (options.keySet + tagField).toList.indexOf(tagName)
    val elems = arena.getHas(variantCell)
    assert(0 <= index && index < elems.length)
    elems(index)
  }

  /**
   * Get the tag associated with a variant.
   *
   * @param arena
   *   current arena
   * @param variantCell
   *   a variant cell
   * @return
   *   the cell that contains the tag value
   */
  def getVariantTag(arena: Arena, variantCell: ArenaCell): ArenaCell = {
    val options = getVariantOptions(variantCell)

    val index = (options.keySet + tagField).toList.indexOf(tagField)
    val elems = arena.getHas(variantCell)
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

  private def expectVariantTag(
      variantCell: ArenaCell,
      options: SortedMap[String, TlaType1],
      tagName: String): Unit = {
    if (!options.contains(tagName)) {
      val variantT = VariantT1(RowT1(options, None))
      val msg = s"Accessing a non-existing variant option via tag $tagName of variant of type $variantT"
      throw new RewriterException(msg, variantCell.toNameEx)
    }
  }

  private def getFieldTypes(cell: ArenaCell): SortedMap[String, TlaType1] = {
    cell.cellType match {
      case CellTFrom(RecRowT1(RowT1(ft, None))) => ft

      case tt =>
        throw new RewriterException(s"Unexpected record type $tt of cell ${cell.id}", cell.toNameEx)
    }
  }

  private def getVariantOptions(cell: ArenaCell): SortedMap[String, TlaType1] = {
    cell.cellType match {
      case CellTFrom(VariantT1(RowT1(opts, None))) => opts

      case tt =>
        throw new RewriterException(s"Unexpected variant type $tt of cell ${cell.id}", cell.toNameEx)
    }
  }
}
