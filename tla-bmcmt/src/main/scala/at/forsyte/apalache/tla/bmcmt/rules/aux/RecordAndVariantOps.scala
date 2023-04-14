package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.types.CellTFrom
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla

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
      nextState = nextState.updateArena(_.appendHasNoSmt(recordCell, FixedElemPtr(fieldCell)))
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
    val (newArena, tagAsCell) = rewriter.modelValueCache.getOrCreate(state.arena, (StrT1.toString, tagName))
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
        makeRecordInternal(nextState, fields + (RecordAndVariantOps.variantTagField -> tagAsCell), variantT)

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
  def getField(arena: PureArenaAdapter, recordCell: ArenaCell, fieldName: String): ArenaCell = {
    val fieldTypes = getFieldTypes(recordCell)
    expectFieldName(recordCell, fieldTypes, fieldName)

    val index = fieldTypes.keySet.toList.indexOf(fieldName)
    val elems = arena.getHas(recordCell)
    assert(0 <= index && index < elems.length)
    elems(index)
  }

  /**
   * Get the variant value by tag. This is an unsafe method, that is, if the associated tag name is different from the
   * provided one, this method returns some value of the proper type (usually, the default value).
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
  def getUnsafeVariantValue(arena: PureArenaAdapter, variantCell: ArenaCell, tagName: String): ArenaCell = {
    val options = getVariantOptions(variantCell)
    expectVariantTag(variantCell, options, tagName)

    val index = (options.keySet + RecordAndVariantOps.variantTagField).toList.indexOf(tagName)
    val elems = arena.getHas(variantCell)
    assert(0 <= index && index < elems.length)
    elems(index)
  }

  /**
   * Return the value associated with the tag, when the tag equals to tagName. Otherwise, return defaultValue.
   *
   * @param state
   *   a symbolic state to start with
   * @param variantCell
   *   an arena cell that holds a variant
   * @param tagName
   *   the tag name
   * @param defaultValue
   *   the value to use when the variant is not tagged with tagName
   * @return
   *   the value associated with the tag, or the default value
   */
  def variantGetOrElse(
      state: SymbState,
      variantCell: ArenaCell,
      tagName: String,
      defaultValue: ArenaCell): SymbState = {
    val tagCell = getVariantTag(state.arena, variantCell)
    val unsafeValueCell = getUnsafeVariantValue(state.arena, variantCell, tagName)
    // IF variant.__tag = tagName THEN variant.__value ELSE defaultValue
    val tagNameOfSort = tla.str(tagName)
    val ite =
      tla
        .ite(tla.eql(tagCell.toBuilder, tagNameOfSort), unsafeValueCell.toBuilder, defaultValue.toBuilder)
    rewriter.rewriteUntilDone(state.setRex(ite))
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
  def getVariantTag(arena: PureArenaAdapter, variantCell: ArenaCell): ArenaCell = {
    val options = getVariantOptions(variantCell)

    val index =
      (options.keySet + RecordAndVariantOps.variantTagField).toList.indexOf(RecordAndVariantOps.variantTagField)
    val elems = arena.getHas(variantCell)
    assert(0 <= index && index < elems.length)
    elems(index)
  }

  /**
   * Filter a set of variants.
   *
   * @param state
   *   a symbolic state
   * @param setCell
   *   the cell that represents the set
   * @param tagName
   *   the tag name of the variants to keep
   * @return
   *   the largest subset of `setCell` that contains the variants that are tagged with `tagName`
   */
  def variantFilter(state: SymbState, setCell: ArenaCell, tagName: String): SymbState = {
    setCell.cellType.toTlaType1 match {
      case SetT1(VariantT1(RowT1(opts, None))) if opts.contains(tagName) =>
        val valueT = opts(tagName)
        var nextState = state.updateArena(_.appendCell(SetT1(valueT)))
        val filteredSetCell = nextState.arena.topCell
        // translate the tag name to a cell
        nextState = getOrCreateVariantTag(nextState, tagName)
        val goalTagAsCell = nextState.asCell

        val variants = nextState.arena.getHas(setCell)
        // get the values unsafely and leave only those values that are produced from the variants tagged with tagName
        val values = variants.map(v => getUnsafeVariantValue(nextState.arena, v, tagName))
        variants.zip(values).foreach { case (variant, value) =>
          val inFiltered = tla.storeInSet(value.toBuilder, filteredSetCell.toBuilder)
          val notInFiltered = tla.storeNotInSet(value.toBuilder, filteredSetCell.toBuilder)
          val inOriginal = tla.selectInSet(variant.toBuilder, setCell.toBuilder)
          val variantTag = getVariantTag(nextState.arena, variant)
          nextState = rewriter.lazyEq.cacheOneEqConstraint(nextState, goalTagAsCell, variantTag)
          val tagsEq = rewriter.lazyEq.safeEq(goalTagAsCell, variantTag)
          val ifCond = tla.and(tagsEq, inOriginal)
          nextState = nextState.updateArena(_.appendHas(filteredSetCell, SmtExprElemPtr(value, ifCond)))
          val storeIf = tla.ite(ifCond, inFiltered, notInFiltered)
          rewriter.solverContext.assertGroundExpr(storeIf)
        }

        nextState.setRex(filteredSetCell.toBuilder)

      case _ =>
        throw new TypingException(s"Expected a set of variants, one of them being $tagName()", state.ex.ID)
    }
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
    val elems = state.arena.getHasPtr(recordCell)
    assert(0 <= index && index < elems.length)

    var nextState = state.updateArena(_.appendCell(recordCell.cellType.toTlaType1))
    val newRecord = nextState.arena.topCell
    // add the fields in the order of their names, update by name
    for ((name, oldPtr) <- fieldTypes.keySet.toSeq.zip(elems)) {
      val updatedPtr = if (name == fieldName) PtrUtil.samePointer(oldPtr)(newCell) else oldPtr
      nextState = nextState.updateArena(_.appendHasNoSmt(newRecord, updatedPtr))
    }

    nextState.setRex(newRecord.toBuilder)
  }

  private def expectFieldName(
      recordCell: ArenaCell,
      fieldTypes: SortedMap[String, TlaType1],
      fieldName: String): Unit = {
    if (!fieldTypes.contains(fieldName)) {
      val recordT = RecRowT1(RowT1(fieldTypes, None))
      val msg = s"Accessing a non-existing field $fieldName of record of type $recordT"
      throw new RewriterException(msg, recordCell.toBuilder)
    }
  }

  private def expectVariantTag(
      variantCell: ArenaCell,
      options: SortedMap[String, TlaType1],
      tagName: String): Unit = {
    if (!options.contains(tagName)) {
      val variantT = VariantT1(RowT1(options, None))
      val msg = s"Accessing a non-existing variant option via tag $tagName of variant of type $variantT"
      throw new RewriterException(msg, variantCell.toBuilder)
    }
  }

  private def getFieldTypes(cell: ArenaCell): SortedMap[String, TlaType1] = {
    cell.cellType match {
      case CellTFrom(RecRowT1(RowT1(ft, None))) => ft

      case tt =>
        throw new RewriterException(s"Unexpected record type $tt of cell ${cell.id}", cell.toBuilder)
    }
  }

  private def getVariantOptions(cell: ArenaCell): SortedMap[String, TlaType1] = {
    cell.cellType match {
      case CellTFrom(VariantT1(RowT1(opts, None))) => opts

      case tt =>
        throw new RewriterException(s"Unexpected variant type $tt of cell ${cell.id}", cell.toBuilder)
    }
  }
}

object RecordAndVariantOps {

  /**
   * The name of the hidden tag field that is attached to every variant.
   */
  val variantTagField = "__tag"
}
