package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.SmtConstElemPtr
import at.forsyte.apalache.tla.bmcmt.rules.aux.AuxOps._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types._

import scala.collection.immutable.SortedMap

/**
 * An element picket that allows us:
 *
 * <ul> <li>to pick from a list of cells instead of a set, and</li> <li>directly uses a choice oracle to avoid multiple
 * comparisons.</li> </ul>
 *
 * @param rewriter
 *   a state rewriter
 * @author
 *   Igor Konnov
 */
class CherryPick(rewriter: SymbStateRewriter) {
  private val protoSeqOps = new ProtoSeqOps(rewriter)
  private val recordOps = new RecordAndVariantOps(rewriter)
  val oracleFactory = new OracleFactory(rewriter)

  /**
   * Determine the type of the set elements an element of this type by introducing an oracle
   *
   * @param set
   *   a set
   * @param state
   *   a symbolic state
   * @param elseAssert
   *   an assertion that is used when the set is empty
   * @return
   *   a new symbolic state whose expression stores a fresh cell that corresponds to the picked element.
   */
  def pick(set: ArenaCell, state: SymbState, elseAssert: TBuilderInstruction): SymbState = {
    set.cellType match {
      // all kinds of sets that should be kept unexpanded
      case PowSetT(t @ SetT1(_)) =>
        // a powerset is never empty, pick an element
        pickFromPowset(CellTFrom(t), set, state)

      case FinFunSetT(CellTFrom(SetT1(argT)), CellTFrom(SetT1(resT))) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT1(argT, resT), set, state)

      case FinFunSetT(CellTFrom(SetT1(argT)), InfSetT(resT)) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT1(argT, resT.toTlaType1), set, state)

      case FinFunSetT(CellTFrom(SetT1(argT)), PowSetT(resultT @ SetT1(_))) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT1(argT, resultT), set, state)

      case FinFunSetT(CellTFrom(SetT1(arg1T)), FinFunSetT(CellTFrom(SetT1(arg2T)), CellTFrom(SetT1(result2T)))) =>
        pickFunFromFunSet(FunT1(arg1T, FunT1(arg2T, result2T)), set, state)

      case FinFunSetT(CellTFrom(SetT1(arg1T)), FinFunSetT(CellTFrom(SetT1(arg2T)), PowSetT(result2T @ SetT1(_)))) =>
        pickFunFromFunSet(FunT1(arg1T, FunT1(arg2T, result2T)), set, state)

      case FinFunSetT(CellTFrom(SetT1(_)), PowSetT(_)) | FinFunSetT(CellTFrom(SetT1(_)), FinFunSetT(_, _)) =>
        throw new RewriterException(s"Rewriting for the type ${set.cellType} is not implemented. Raise an issue.",
            state.ex)

      case InfSetT(CellTFrom(IntT1)) if set == state.arena.cellIntSet() || set == state.arena.cellNatSet() =>
        // pick an integer or natural
        pickFromIntOrNatSet(set, state)

      case _ =>
        val elems = state.arena.getHas(set)
        if (elems.isEmpty) {
          throw new RuntimeException(s"The set $set is statically empty. Pick should not be called on that.")
        }

        val (nextState, oracle) = oracleFactory.newDefaultOracle(state, elems.size + 1)

        // pick only the elements that belong to the set
        val elemsIn = elems.map { c => tla.selectInSet(c.toBuilder, set.toBuilder) }
        rewriter.solverContext.assertGroundExpr(oracle.caseAssertions(nextState, elemsIn :+ elseAssert))

        pickByOracle(nextState, oracle, elems, elseAssert)
    }
  }

  /**
   * Determine the type of the set elements and pick an element of this type.
   *
   * Warning: this method does not check, whether the picked element actually belongs to the set. You have to do it
   * yourself.
   *
   * @param state
   *   a symbolic state
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param elems
   *   a non-empty set of cells
   * @return
   *   a new symbolic state whose expression stores a fresh cell that corresponds to the picked element.
   */
  def pickByOracle(
      state: SymbState,
      oracle: Oracle,
      elems: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    assert(elems.nonEmpty) // this is an advanced operator -- you should know what you are doing
    val targetType = elems.head.cellType

    // Optimization 1: if the (multi-) set consists of identical cells, return the cell
    // (e.g., this happens when all enabled transitions do not change a variable.)
    if (elems.distinct.size == 1) {
      return state.setRex(elems.head.toBuilder)
    }

    // Optimization 2: if some cells coincide, group them via ZipOracle.
    // This optimization gives us a 20% speed up on a small set of benchmarks.
    val groups = elems.indices.groupBy(elems(_))
    if (groups.size < elems.size) {
      val zipOracle = new ZipOracle(oracle,
          // Sort indices, it determines the order of SMT disjuncts generated by the oracle;
          // See https://github.com/informalsystems/apalache/issues/2120
          groups.values.toSeq.map(_.sorted))
      return pickByOracle(state, zipOracle, groups.keys.toSeq, elseAssert)
    }

    // the general case
    targetType match {
      case CellTFrom(tt @ (ConstT1(_) | StrT1 | IntT1 | BoolT1)) =>
        pickBasic(tt, state, oracle, elems, elseAssert)

      case CellTFrom(t @ TupT1(_ @_*)) =>
        pickTuple(t, state, oracle, elems, elseAssert)

      case CellTFrom(RecT1(_)) =>
        pickOldRecord(state, oracle, elems, elseAssert)

      case CellTFrom(RecRowT1(_)) =>
        pickRecord(state, oracle, elems, elseAssert)

      case CellTFrom(VariantT1(_)) =>
        pickVariant(state, oracle, elems, elseAssert)

      case CellTFrom(t @ SetT1(_)) =>
        pickSet(t, state, oracle, elems, elseAssert)

      case CellTFrom(t @ SeqT1(_)) =>
        pickSequence(t, state, oracle, elems, elseAssert)

      case CellTFrom(t @ FunT1(_, _)) =>
        pickFun(t, state, oracle, elems, elseAssert)

      case _ =>
        throw new RewriterException("Do not know how pick an element from a set of type: " + targetType, state.ex)
    }
  }

  /**
   * Pick a basic value, that is, an integer, Boolean, or constant.
   *
   * @param cellType
   *   a cell type to assign to the picked cell.
   * @param state
   *   a symbolic state
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param elems
   *   a sequence of elements of cellType
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickBasic(
      cellType: TlaType1,
      state: SymbState,
      oracle: Oracle,
      elems: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, elems.map(_.toString).mkString(", ")))
    val arena = state.arena.appendCell(cellType)
    val resultCell = arena.topCell
    // compare the set contents with the result
    val eqState = rewriter.lazyEq.cacheEqConstraints(state, elems.map(e => (e, resultCell)))
    // the new element equals to an existing element in the set
    val asserts = elems.map { el => rewriter.lazyEq.safeEq(resultCell, el) }
    rewriter.solverContext.assertGroundExpr(oracle.caseAssertions(eqState, asserts :+ elseAssert))

    rewriter.solverContext.log(s"; } CHERRY-PICK $resultCell:$cellType")
    eqState.setArena(arena).setRex(resultCell.toBuilder)
  }

  /**
   * Implements SE-PICK-TUPLE.
   *
   * @param cellType
   *   a cell type to assign to the picked cell.
   * @param state
   *   a symbolic state
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param tuples
   *   a sequence of records of cellType
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickTuple(
      cellType: TupT1,
      state: SymbState,
      oracle: Oracle,
      tuples: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, tuples.map(_.toString).mkString(", ")))
    var newState = state

    def pickAtPos(i: Int): ArenaCell = {
      // as we know the field index, we just directly project tuples on this index
      val slice = tuples.map(c => newState.arena.getHas(c)(i))
      newState = pickByOracle(newState, oracle, slice, elseAssert)
      newState.asCell
    }

    // introduce a new tuple
    newState = newState.setArena(newState.arena.appendCell(cellType))
    val newTuple = newState.arena.topCell
    // for each index i, pick a value from the projection { t[i] : t \in tuples }
    val newFields = cellType.elems.indices.map(pickAtPos).map { SmtConstElemPtr }

    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element t[i], as it will use the same oracle!

    // add the new fields to arena
    val newArena = newState.arena.appendHasNoSmt(newTuple, newFields: _*)
    rewriter.solverContext.log(s"; } CHERRY-PICK $newTuple:$cellType")
    newState
      .setArena(newArena)
      .setRex(newTuple.toBuilder)

  }

  /**
   * Implements SE-PICK-RECORD.
   *
   * Note that some record fields may have bogus values, since not all the records in the set are required to have all
   * the keys assigned. That is an unavoidable loophole in the record types.
   *
   * @param state
   *   a symbolic state
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param records
   *   a sequence of records of cellType
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickOldRecord(
      state: SymbState,
      oracle: Oracle,
      records: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    // the records do not always have the same type, but they do have compatible types
    val commonRecordT = findCommonRecordType(records)
    rewriter.solverContext
      .log("; CHERRY-PICK %s FROM [%s] {".format(commonRecordT, records.map(_.toString).mkString(", ")))

    def findKeyIndex(recT: RecT1, key: String): Int =
      recT.fieldTypes.keySet.toList.indexOf(key)

    var newState = state

    def getKeyOrDefault(record: ArenaCell, key: String): ArenaCell = {
      val thisRecT = record.cellType.toTlaType1.asInstanceOf[RecT1]
      if (thisRecT.fieldTypes.contains(key)) {
        val keyIndex = findKeyIndex(thisRecT, key)
        val edges = newState.arena.getHas(record)
        try {
          edges(keyIndex)
        } catch {
          case _: IndexOutOfBoundsException =>
            // TODO Remove once sound record typing is implemented
            val url =
              "https://apalache.informal.systems/docs/apalache/known-issues.html#updating-records-with-excess-fields"
            val msg =
              s"""|An updated record has more fields than its declared type:
                  |A record with the inferred type `$thisRecT` has been updated with
                  |the key `${key}` in an `EXCEPT` expression and the updated record has more fields
                  |than are specified in its type annotation. For details see $url""".stripMargin.linesIterator
                .mkString(" ")
                .trim
            throw new MalformedSepecificationError(msg)
        }
      } else {
        // This record does not have the key, but it was mixed with other records and produced a more general type.
        // Return a default value. As we are iterating over fields of commonRecordT, we will always find a value.
        val valueT = commonRecordT.fieldTypes(key)
        val (newArena, defaultValue) = rewriter.defaultValueCache.getOrCreate(newState.arena, valueT)
        newState = newState.setArena(newArena)
        defaultValue
      }
    }

    def pickAtPos(key: String): ArenaCell = {
      val slice = records.map(c => getKeyOrDefault(c, key))
      newState = pickByOracle(newState, oracle, slice, elseAssert)
      newState.asCell
    }

    // introduce a new record
    newState = newState.setArena(newState.arena.appendCell(commonRecordT))
    val newRecord = newState.arena.topCell
    // pick the domain using the oracle.
    newState = pickRecordDomain(
        commonRecordT,
        CellTFrom(SetT1(StrT1)),
        newState,
        oracle,
        records.map(r => newState.arena.getDom(r)),
    )
    val newDom = newState.asCell
    // pick the fields using the oracle
    val fieldCells = commonRecordT.fieldTypes.keySet.toSeq.map(pickAtPos).map(SmtConstElemPtr)
    // and connect them to the record
    var newArena = newState.arena.setDom(newRecord, newDom)
    newArena = newArena.appendHasNoSmt(newRecord, fieldCells: _*)
    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element r.key, as it will use the same oracle!

    rewriter.solverContext.log(s"; } CHERRY-PICK $newRecord:$commonRecordT")

    newState
      .setArena(newArena)
      .setRex(newRecord.toBuilder)
  }

  /**
   * Picks a record from a sequence of records.
   *
   * @param state
   *   a symbolic state
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param records
   *   a sequence of records of cellType
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickRecord(
      state: SymbState,
      oracle: Oracle,
      records: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    // new row records always have the same type
    val (fieldTypes, recordT) = records.head.cellType match {
      case CellTFrom(rt @ RecRowT1(RowT1(fieldTypes, None))) => (fieldTypes, rt)
      case tt => throw new IllegalArgumentException("Unexpected record type: " + tt)
    }
    rewriter.solverContext
      .log("; CHERRY-PICK %s FROM [%s] {".format(recordT, records.map(_.toString).mkString(", ")))

    var nextState = state

    // project all records on a single field and pick the value according to the oracle
    def projectOnField(fieldName: String): ArenaCell = {
      val projection = records.map(cell => recordOps.getField(nextState.arena, cell, fieldName))
      nextState = pickByOracle(nextState, oracle, projection, elseAssert)
      nextState.asCell
    }

    // introduce a new record
    nextState = nextState.setArena(nextState.arena.appendCell(recordT))
    val newRecord = nextState.arena.topCell
    // pick the fields using the oracle and connect them to the record
    val pickedFieldValues = fieldTypes.keySet.toSeq.map(projectOnField).map(SmtConstElemPtr)
    nextState = nextState.updateArena(_.appendHasNoSmt(newRecord, pickedFieldValues: _*))
    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element r.key, as it will use the same oracle!
    rewriter.solverContext.log(s"; } CHERRY-PICK $newRecord:$recordT")

    nextState.setRex(newRecord.toBuilder)
  }

  /**
   * Picks a variant from a sequence of variants.
   *
   * @param state
   *   a symbolic state
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param variants
   *   a sequence of records of cellType
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickVariant(
      state: SymbState,
      oracle: Oracle,
      variants: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    // variants should always have the same type
    val (optionTypes, variantT) = variants.head.cellType match {
      case CellTFrom(rt @ VariantT1(RowT1(opts, None))) => (opts, rt)
      case tt => throw new IllegalArgumentException("Unexpected variant type: " + tt)
    }
    rewriter.solverContext
      .log("; CHERRY-PICK %s FROM [%s] {".format(variantT, variants.map(_.toString).mkString(", ")))

    var nextState = state

    // project all records on a single tag and pick the value according to the oracle
    def pickValueByTag(tagName: String): ArenaCell = {
      val projection = variants.map(cell => recordOps.getUnsafeVariantValue(nextState.arena, cell, tagName))
      nextState = pickByOracle(nextState, oracle, projection, elseAssert)
      nextState.asCell
    }

    val pickedTag: ArenaCell = {
      val tags = variants.map(c => recordOps.getVariantTag(nextState.arena, c))
      nextState = pickByOracle(nextState, oracle, tags, elseAssert)
      nextState.asCell
    }

    // introduce a new variant
    nextState = nextState.setArena(nextState.arena.appendCell(variantT))
    val newVariant = nextState.arena.topCell
    // pick the values using the oracle and connect them to the variant
    val pickedValuesAndTag = (optionTypes.keySet + RecordAndVariantOps.variantTagField).toSeq
      .map { key =>
        if (key == RecordAndVariantOps.variantTagField) {
          pickedTag
        } else {
          pickValueByTag(key)
        }
      }
      .map(SmtConstElemPtr)
    nextState = nextState.updateArena(_.appendHasNoSmt(newVariant, pickedValuesAndTag: _*))
    rewriter.solverContext.log(s"; } CHERRY-PICK $newVariant:$variantT")

    nextState.setRex(newVariant.toBuilder)
  }

  /**
   * Pick a set among a sequence of record domains. We know that the types of all the domains are compatible. Moreover,
   * from the record constructor, we know that the record domains have exactly the same sequence of keys in the arena.
   * Hence, we only have to define the SMT constraints that regulate which keys belong to the new set. This optimization
   * prevents the model checker from blowing up in the number of record domains, e.g., in Raft.
   *
   * @param domType
   *   the goal type
   * @param state
   *   a symbolic state
   * @param oracle
   *   the oracle to use
   * @param domains
   *   the domains to pick from
   * @return
   *   a new cell that encodes a picked domain
   */
  private def pickRecordDomain(
      commonRecordType: RecT1,
      domType: CellT,
      state: SymbState,
      oracle: Oracle,
      domains: Seq[ArenaCell]): SymbState = {
    // It often happens that all the domains are actually the same cell. Return this cell.
    val distinct = domains.distinct
    if (distinct.size == 1) {
      state.setRex(distinct.head.toBuilder)
    } else {
      val (newState, keyToCell) = findRecordKeys(state, commonRecordType)
      // Introduce a new cell for the picked domain
      var nextState = newState.updateArena(_.appendCellOld(domType))
      val newDom = nextState.arena.topCell
      // Add the cells for all potential keys.
      // Importantly, they all come from strValueCache, so the same key produces the same cell.
      val keyCells = keyToCell.values.toSeq
      nextState = nextState.updateArena(_.appendHas(newDom, keyCells.map(SmtConstElemPtr): _*))
      // Constrain membership with SMT
      for ((dom, no) <- domains.zipWithIndex) {
        val domainCells = nextState.arena.getHas(dom)

        for (keyCell <- keyCells) {
          // Although we search over a list, the list size is usually small, e.g., up to 10 elements
          if (domainCells.contains(keyCell)) {
            // The key belongs to the new domain only if it belongs to the domain that is pointed by the oracle
            val ite = tla.ite(tla.selectInSet(keyCell.toBuilder, dom.toBuilder),
                tla.storeInSet(keyCell.toBuilder, newDom.toBuilder),
                tla.storeNotInSet(keyCell.toBuilder, newDom.toBuilder))
            val unchangedSet = rewriter.solverContext.config.smtEncoding match {
              case SMTEncoding.Arrays =>
                // In the arrays encoding we need to propagate the SSA representation of the array if nothing changes
                tla.storeNotInSet(keyCell.toBuilder, newDom.toBuilder)
              case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
                tla.bool(true)
              case oddEncodingType =>
                throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
            }
            rewriter.solverContext
              .assertGroundExpr(
                  tla.ite(
                      oracle.whenEqualTo(nextState, no),
                      ite,
                      unchangedSet,
                  )
              )
          } else {
            // The domain pointed by the oracle does not contain the key
            val notInDom = tla.not(tla.selectInSet(keyCell.toBuilder, newDom.toBuilder))
            rewriter.solverContext.assertGroundExpr(
                tla.impl(
                    oracle.whenEqualTo(nextState, no),
                    notInDom,
                )
            )
          }
        }
      }
      nextState.setRex(newDom.toBuilder)
    }
  }

  private def findCommonRecordType(records: Seq[ArenaCell]): RecT1 = {
    var maxRecordType = records.head.cellType.toTlaType1
    // This is temporary plumbing for backward compatibility with the old records.
    // It will be removed soon: https://github.com/informalsystems/apalache/issues/401.
    val unifier = new TypeUnifier(new TypeVarPool())
    for (rec <- records.tail) {
      val recType = rec.cellType.toTlaType1
      unifier.unify(Substitution(), maxRecordType, recType) match {
        case Some((_, commonType)) =>
          maxRecordType = commonType

        case None =>
          throw new IllegalStateException(s"Found inconsistent records in a set: $maxRecordType and $recType")
      }
    }
    maxRecordType.asInstanceOf[RecT1]
  }

  // find the union of the keys for all records, if it exists
  private def findRecordKeys(state: SymbState, recordType: RecT1): (SymbState, SortedMap[String, ArenaCell]) = {
    val commonKeys = recordType.fieldTypes.keySet
    var keyToCell = SortedMap[String, ArenaCell]()
    var nextState = state
    for (key <- commonKeys) {
      val (newArena, cell) = rewriter.modelValueCache.getOrCreate(nextState.arena, (StrT1.toString, key))
      keyToCell = keyToCell + (key -> cell)
      nextState = nextState.setArena(newArena)
    }

    (nextState, keyToCell)
  }

  /**
   * Implements SE-PICK-SET.
   *
   * Note that some record fields may have bogus values, since not all the records in the set are required to have all
   * the keys assigned. That is an unavoidable loophole in the record types.
   *
   * @param cellType
   *   a cell type to assign to the picked cell.
   * @param state
   *   a symbolic state
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param memberSets
   *   a sequence of sets of cellType
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickSet(
      cellType: SetT1,
      state: SymbState,
      oracle: Oracle,
      memberSets: Seq[ArenaCell],
      elseAssert: TBuilderInstruction,
      noSmt: Boolean = false): SymbState = {
    if (memberSets.isEmpty) {
      throw new RuntimeException("Picking from a statically empty set")
    } else if (memberSets.length == 1) {
      // one set, either empty, or not
      state.setRex(memberSets.head.toBuilder)
    } else if (memberSets.distinct.length == 1) {
      // all sets are actually the same, this is quite common for function domains
      state.setRex(memberSets.head.toBuilder)
    } else if (memberSets.forall(ms => state.arena.getHas(ms).isEmpty)) {
      // multiple sets that are statically empty, just pick the first one
      state.setRex(memberSets.head.toBuilder)
    } else {
      pickSetNonEmpty(cellType, state, oracle, memberSets, elseAssert, noSmt)
    }
  }

  private def pickSetNonEmpty(
      cellType: SetT1,
      state: SymbState,
      oracle: Oracle,
      memberSets: Seq[ArenaCell],
      elseAssert: TBuilderInstruction,
      noSMT: Boolean): SymbState = {
    def solverAssert(e: TlaEx): Unit = rewriter.solverContext.assertGroundExpr(e)

    rewriter.solverContext
      .log("; CHERRY-PICK %s FROM [%s] {".format(cellType, memberSets.map(_.toString).mkString(", ")))
    var nextState = state
    // introduce a fresh cell for the set
    nextState = nextState.setArena(state.arena.appendCell(cellType))
    val resultCell = nextState.arena.topCell

    // get all the cells pointed by the elements of every member set
    val elemsOfMemberSets: Seq[Seq[ArenaCell]] = memberSets.map(s => Set(nextState.arena.getHas(s): _*).toSeq)

    // Here we are using the awesome linear encoding that uses interleaving.
    // We give an explanation for two statically non-empty sets, statically empty sets should be treated differently.
    // Assume S_1 = { c_1, ..., c_n } and S_2 = { d_1, ..., d_n } (pad if they have different lengths)
    //
    // We construct a new set R = { z_1, ..., z_n } where z_i = FROM { c_i, d_i }
    //
    // The principal constraint: chosen = 1 => in(S_1, S) /\ chosen = 2 => in(S_2, S)
    //
    // Here are the additional constraints for i \in 1..n:
    //
    // ChooseProper: chosen = 1 => z_i = c_i /\ chosen = 2 => z_i = d_i
    // ChooseIn:     in(z_i, R) <=> (chosen = 1 /\ in(c_i, S_1) \/ (chosen = 2 /\ in(d_i, S_2)

    val maxLen = elemsOfMemberSets.map(_.size).reduce((i, j) => if (i > j) i else j)
    assert(maxLen != 0)
    val maxPadded = elemsOfMemberSets.find(_.size == maxLen).get // existence is guaranteed by maxLen

    // pad a non-empty sequence to the given length, keep the empty sequence intact
    def padNonEmptySeq(s: Seq[ArenaCell], len: Int): Seq[ArenaCell] = s match {
      // copy last as many times as needed
      case allButLast :+ last => allButLast ++ Seq.fill(len - allButLast.length)(last)
      // the empty sequence is a special case
      case Nil => maxPadded
    }

    val paddedOfMemberSets = elemsOfMemberSets.map(padNonEmptySeq(_, maxLen))
    // for each index i, pick from {c_i, ..., d_i}.
    def pickOneElement(i: Int): Unit = {
      val toPickFrom = paddedOfMemberSets.map { _(i) }
      nextState = pickByOracle(nextState, oracle, toPickFrom, elseAssert)
      val picked = nextState.asCell

      // this property is enforced by the oracle magic: chosen = 1 => z_i = c_i /\ chosen = 2 => z_i = d_i

      // The awesome property of the oracle is that we do not have to compare the sets directly!
      // Instead, we compare the oracle values.
      // (chosen = 1 /\ in(z_i, R) <=> in(c_i, S_1)) \/ (chosen = 2 /\ in(z_i, R) <=> in(d_i, S_2)) \/ (chosen = N <=> elseAssert)
      def nthIn(elemAndSet: (ArenaCell, ArenaCell), no: Int): (TBuilderInstruction, TBuilderInstruction) = {
        if (elemsOfMemberSets(no).nonEmpty) {
          val inSet = tla.ite(tla.selectInSet(elemAndSet._1.toBuilder, elemAndSet._2.toBuilder),
              tla.storeInSet(picked.toBuilder, resultCell.toBuilder),
              tla.storeNotInSet(picked.toBuilder, resultCell.toBuilder))
          val unchangedSet = rewriter.solverContext.config.smtEncoding match {
            case SMTEncoding.Arrays =>
              // In the arrays encoding we need to propagate the SSA representation of the array if nothing changes
              tla.storeNotInSet(picked.toBuilder, resultCell.toBuilder)
            case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
              tla.bool(true)
            case oddEncodingType =>
              throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
          }
          (inSet, unchangedSet)
        } else {
          // nothing belongs to the set
          (tla.storeNotInSet(picked.toBuilder, resultCell.toBuilder), tla.bool(true))
        }
      }

      // add the cell to the arena
      nextState = nextState.updateArena(_.appendHas(resultCell, SmtConstElemPtr(picked)))
      if (!noSMT) { // add the SMT constraints
        val assertions = (toPickFrom.zip(memberSets).zipWithIndex.map((nthIn _).tupled)).unzip
        // (chosen = 1 /\ in(z_i, R) = in(c_i, S_1)) \/ (chosen = 2 /\ in(z_i, R) = in(d_i, S_2))
        val membershipAssertions = assertions._1
        val nonMembershipAssertions = assertions._2
        solverAssert(oracle.caseAssertions(nextState, membershipAssertions :+ elseAssert,
                nonMembershipAssertions :+ tla.bool(true)))
      }
    }

    0.until(maxLen).foreach(pickOneElement)

    rewriter.solverContext.log(s"; } CHERRY-PICK $resultCell:$cellType")
    nextState.setRex(resultCell.toBuilder)
  }

  /**
   * Picks a sequence from a list of sequences
   *
   * @param cellType
   *   a cell type to assign to the picked cell.
   * @param state
   *   a symbolic state
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param memberSeqs
   *   a sequence of sequences of cellType
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickSequence(
      cellType: SeqT1,
      state: SymbState,
      oracle: Oracle,
      memberSeqs: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    if (memberSeqs.isEmpty) {
      throw new RuntimeException("Picking a sequence from a statically empty set")
    } else if (memberSeqs.length == 1) {
      // one sequence, either empty, or not
      state.setRex(memberSeqs.head.toBuilder)
    } else if (memberSeqs.distinct.length == 1) {
      // all sequences are actually the same cell
      state.setRex(memberSeqs.head.toBuilder)
    } else if (memberSeqs.forall(ms => protoSeqOps.unpackSeq(state.arena, ms)._3 == 0)) {
      // multiple sequences that have capacity of 0
      state.setRex(memberSeqs.head.toBuilder)
    } else {
      pickSequenceNonEmpty(cellType, state, oracle, memberSeqs, elseAssert)
    }
  }

  // Pick from a sequences of sequences
  private def pickSequenceNonEmpty(
      seqType: SeqT1,
      state: SymbState,
      oracle: Oracle,
      memberSeqs: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    rewriter.solverContext
      .log("; CHERRY-PICK %s FROM [%s] {".format(seqType, memberSeqs.map(_.toString).mkString(", ")))

    // get all the cells pointed by the elements of every member set, without changing their order!
    val elemsOfMemberSeqs: Seq[Seq[ArenaCell]] = memberSeqs.map { seq =>
      val protoSeq = protoSeqOps.fromSeq(state.arena, seq)
      protoSeqOps.elems(state.arena, protoSeq)
    }

    // extract lengths of all sequences
    val memberLengths = memberSeqs.map { seq =>
      protoSeqOps.seqLen(state.arena, seq)
    }

    // we need the default value to pad the shorter sequences
    val (newArena, defaultValue) =
      rewriter.defaultValueCache.getOrCreate(state.arena, seqType.elem)
    var nextState = state.setArena(newArena)

    // Here we are using the awesome linear encoding that uses interleaving.
    // We give an explanation for two statically non-empty sequences, the static case should be handled differently.
    // Assume S_1 = << c_1, ..., c_n >> and S_2 = << d_1, ..., d_n >> (pad if they have different lengths)
    //
    // We construct a new sequence R = << z_1, ..., z_n >> where z_i = FROM { c_i, d_i }
    //
    // As we are not tracking membership for sequences, no additional SMT constraints are needed
    val maxCapacity = elemsOfMemberSeqs.map(_.size).reduce(Math.max)
    assert(maxCapacity != 0)

    def padSeq(s: Seq[ArenaCell]): Seq[ArenaCell] = {
      if (s.length >= maxCapacity) {
        s
      } else {
        s ++ Seq.fill(maxCapacity - s.length)(defaultValue)
      }
    }

    val paddedSeqElems = elemsOfMemberSeqs.map(padSeq)
    // Now we have all sequences of the same length. Hence, we can transpose them:
    // List(a_1, ..., a_n),
    // List(b_1, ..., b_n),
    // ...
    // List(z_1, ..., z_n)
    // becomes
    // List(a_1, b_1, ..., z_1),
    // List(a_2, b_2, ..., z_2),
    // ...
    // List(a_n, b_n, ..., z_n),
    val transposed = paddedSeqElems.transpose

    // for each index i, pick from {a_i, ..., z_i}.
    def pickOneElement(state: SymbState, indexBase1: Int): (SymbState, ArenaCell) = {
      val toPickFrom = transposed(indexBase1 - 1)
      // the oracle magic guarantees us that: oracle = 0 => picked = a_i /\ oracle = 1 => picked = b_i /\ ...
      val newState = pickByOracle(state, oracle, toPickFrom, elseAssert)
      (newState, newState.asCell)
    }

    // construct a proto sequence by picking elements for 1..maxCapacity
    nextState = protoSeqOps.make(nextState, maxCapacity, pickOneElement)
    val protoSeq = nextState.asCell
    // pick the length
    nextState = pickBasic(IntT1, nextState, oracle, memberLengths, elseAssert)
    val length = nextState.asCell
    // construct the sequence
    nextState = protoSeqOps.mkSeq(nextState, seqType, protoSeq, length)

    rewriter.solverContext.log(s"; } CHERRY-PICK $nextState:$seqType")
    nextState
  }

  /**
   * Picks a function from a set.
   *
   * @param funType
   *   a cell type to assign to the picked cell.
   * @param oracle
   *   a variable that stores which element (by index) should be picked, can be unrestricted
   * @param funs
   *   a sequence of cells that store functions
   * @param state
   *   a symbolic state
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickFun(
      funType: FunT1,
      state: SymbState,
      oracle: Oracle,
      funs: Seq[ArenaCell],
      elseAssert: TBuilderInstruction): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(funType, funs.map(_.toString).mkString(", ")))
    var nextState = state
    rewriter.solverContext.config.smtEncoding match {
      case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
        // We create an unconstrained SMT array that can be equated to the cells of funs for the oracle assertions
        nextState = nextState.updateArena(_.appendCell(funType, isUnconstrained = true))
        val funCell = nextState.arena.topCell

        // Pick a function in funs and generate a SMT equality between it and funCell
        val asserts = funs.map { el => tla.eql(funCell.toBuilder, el.toBuilder) }
        rewriter.solverContext.assertGroundExpr(oracle.caseAssertions(nextState, asserts :+ elseAssert))

        // Propagate the picked function's domain, by relying on the same oracle used to pick the function
        val domT = SetT1(funType.arg)
        nextState = pickSet(domT, nextState, oracle, funs.map(nextState.arena.getDom), elseAssert)
        val pickedDom = nextState.asCell
        nextState = nextState.updateArena(_.setDom(funCell, pickedDom))

        // Propagate the picked function's relation, by relying on the same oracle used to pick the function
        val relationT = SetT1(TupT1(funType.arg, funType.res))
        nextState = pickSet(
            relationT,
            nextState,
            oracle,
            funs.map(nextState.arena.getCdm),
            elseAssert,
            noSmt = true,
        )
        val pickedRelation = nextState.asCell
        nextState = nextState.updateArena(_.setCdm(funCell, pickedRelation))
        // For the decoder to work, the relation's arguments may need to be equated to the domain elements
        nextState = constrainRelationArgs(nextState, rewriter, pickedDom, pickedRelation)

        // The function's relation is used by the decoder to produce counter-examples. The first elements of its tuples
        // have to be equated to the function's domain, otherwise some tuples might be erroneously filtered out by the
        // decoder, leading to spurious counter-examples.
        nextState = nextState.updateArena(_.appendCell(pickedDom.cellType.toTlaType1))
        val domFromPickedRelation = nextState.arena.topCell
        val domElemsFromPickedRelation =
          nextState.arena.getHas(pickedRelation).map(e => nextState.arena.getHasPtr(e).head)
        nextState = nextState.updateArena(_.appendHas(domFromPickedRelation, domElemsFromPickedRelation: _*))
        nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((pickedDom, domFromPickedRelation)))
        rewriter.lazyEq.safeEq(pickedDom, domFromPickedRelation)

        rewriter.solverContext.log(s"; } CHERRY-PICK $funCell:$funType")
        // That's it!
        nextState.setRex(funCell.toBuilder)

      case SMTEncoding.OOPSLA19 =>
        // Pick the relation
        val relationT = SetT1(TupT1(funType.arg, funType.res))
        nextState = pickSet(relationT, nextState, oracle, funs.map(nextState.arena.getCdm), elseAssert)
        val pickedRelation = nextState.asCell
        // Create a fresh cell to hold the function
        nextState = nextState.setArena(nextState.arena.appendCell(funType))
        val funCell = nextState.arena.topCell
        val newArena = nextState.arena.setCdm(funCell, pickedRelation)
        rewriter.solverContext.log(s"; } CHERRY-PICK $funCell:$funType")
        // That's it!
        nextState.setArena(newArena).setRex(funCell.toBuilder)

      case oddEncodingType =>
        throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
    }
  }

  /**
   * Implements SE-PICK-SET, that is, assume that the picked element is a set itself.
   *
   * @param resultType
   *   a cell type to assign to the picked cell.
   * @param set
   *   a powerset
   * @param state
   *   a symbolic state
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickFromPowset(resultType: CellT, set: ArenaCell, state: SymbState): SymbState = {
    rewriter.solverContext.log("; PICK %s FROM %s {".format(resultType, set))
    var nextState = state
    nextState = nextState.updateArena(_.appendCellOld(resultType))
    val resultSet = nextState.arena.topCell
    val baseSet = nextState.arena.getDom(set)
    val elems = nextState.arena.getHasPtr(baseSet)
    // resultSet may contain all the elements from the baseSet of the powerset SUBSET(S)
    nextState = nextState.updateArena(_.appendHas(resultSet, elems: _*))

    // if resultSet has an element, then it must be also in baseSet
    def inResultIfInBase(elem: ArenaCell): Unit = {
      // In the oopsla19 encoding resultSet is initially unconstrained, and thus can contain any combination of elems.
      // To emulate this in the arrays encoding, in which the all sets are initially empty, unconstrained predicates
      // are used to allow the SMT solver to consider all possible combinations of elems.
      if (rewriter.solverContext.config.smtEncoding == SMTEncoding.Arrays) {
        nextState = nextState.updateArena(_.appendCell(BoolT1))
        val pred = nextState.arena.topCell.toBuilder
        val storeElem = tla.storeInSet(elem.toBuilder, resultSet.toBuilder)
        val notStoreElem = tla.storeNotInSet(elem.toBuilder, resultSet.toBuilder)
        rewriter.solverContext.assertGroundExpr(tla.ite(pred, storeElem, notStoreElem))
      }

      val inResult = tla.selectInSet(elem.toBuilder, resultSet.toBuilder)
      val inBase = tla.selectInSet(elem.toBuilder, baseSet.toBuilder)
      rewriter.solverContext.assertGroundExpr(tla.impl(inResult, inBase))
    }

    elems.foreach(e => inResultIfInBase(e.elem))
    rewriter.solverContext.log("; } PICK %s FROM %s".format(resultType, set))
    nextState.setRex(resultSet.toBuilder)
  }

  /**
   * Picks a function from a set [S -> T]. Since [S -> T] is in its unexpanded form, it is easy to pick a function by
   * imposing the constraints from S and T, so we are not using an oracle here. However, we have to take care of T, as
   * it can be an unexpanded set itself, e.g., SUBSET X, or [X -> Y].
   *
   * @param funT
   *   a cell type to assign to the picked cell.
   * @param funSet
   *   a function set [S -> T]
   * @param state
   *   a symbolic state
   * @return
   *   a new symbolic state with the expression holding a fresh cell that stores the picked element.
   */
  def pickFunFromFunSet(funT: FunT1, funSet: ArenaCell, state: SymbState): SymbState = {
    rewriter.solverContext.log("; PICK %s FROM %s {".format(funT, funSet))
    val dom = state.arena.getDom(funSet)
    // Get the set of potential arguments, always expanded! Remove the duplicates.
    val (newState, nonDups) = new SetOps(rewriter).dedup(state, dom)
    var nextState = newState
    val cdm = state.arena.getCdm(funSet) // this is a set of potential results, may be expanded, may be not.
    // create the function cell
    nextState = nextState.updateArena(_.appendCell(funT))
    val funCell = nextState.arena.topCell
    // create the relation cell
    nextState = nextState.updateArena(_.appendCell(SetT1(TupT1(funT.arg, funT.res))))
    val relationCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.setDom(funCell, dom).setCdm(funCell, relationCell))
    // For the decoder to work, the relation's arguments may need to be equated to the domain elements
    nextState = constrainRelationArgs(nextState, rewriter, dom, relationCell)

    // For every domain cell, pick a result from the co-domain.
    // The beauty of CherryPick: when the co-domain is not expanded, CherryPick will pick one value out of the co-domain,
    // instead of constructing the co-domain first.
    for ((arg, isNonDup) <- nextState.arena.getHasPtr(dom).zip(nonDups)) {
      nextState = pick(cdm, nextState, nextState.arena.cellFalse().toBuilder) // the co-domain should be non-empty
      val pickedResult = nextState.asCell

      nextState = nextState.updateArena(_.appendCell(TupT1(funT.arg, funT.res)))
      val pair = nextState.arena.topCell

      rewriter.solverContext.config.smtEncoding match {
        case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
          // We carry the metadata here
          nextState = nextState.updateArena(_.appendHasNoSmt(pair, arg, SmtConstElemPtr(pickedResult)))
          nextState = nextState.updateArena(_.appendHasNoSmt(relationCell, SmtConstElemPtr(pair)))
          // We update the SMT array here
          // We don't use isNonDup because writing on an array entry twice has no adverse effect, if pickedResult is valid
          val store = tla.storeInSet(pickedResult.toBuilder, funCell.toBuilder, arg.elem.toBuilder)
          rewriter.solverContext.assertGroundExpr(store)

          cdm.cellType match {
            case _: PowSetT =>
              val powSetDom = nextState.arena.getDom(cdm)
              // TODO: rewrite and remove SetInclusionRuleWithArrays
              // Currently not possible because we cannot generate unique names to bind a universal quantifier
              val appFunResInDom = tla.subseteq(pickedResult.toBuilder, powSetDom.toBuilder)
              nextState = rewriter.rewriteUntilDone(nextState.setRex(appFunResInDom))
              val resCell = nextState.asCell
              rewriter.solverContext.assertGroundExpr(resCell.toBuilder)

            case _: FinFunSetT =>
              nextState = pick(cdm, nextState, nextState.arena.cellFalse().toBuilder)
              val recursivelyPickedFun = nextState.asCell
              rewriter.solverContext.assertGroundExpr(tla.eql(pickedResult.toBuilder, recursivelyPickedFun.toBuilder))

            case _: InfSetT =>
              nextState = nextState.updateArena(_.appendCellOld(cdm.cellType.asInstanceOf[InfSetT].elemType))
              val unboundElem = nextState.asCell
              val eql = tla.eql(pickedResult.toBuilder, unboundElem.toBuilder)
              val ge = tla.ge(unboundElem.toBuilder, tla.int(0))
              rewriter.solverContext.assertGroundExpr(eql)
              if (cdm == state.arena.cellNatSet()) rewriter.solverContext.assertGroundExpr(ge) // Add Nat constraint

            case _ =>
              if (rewriter.solverContext.config.smtEncoding == SMTEncoding.FunArrays) {
                // Since the cmd set is not an SMT array, we have to use lazy equality
                val cmdElems = nextState.arena.getHas(cdm)
                nextState = rewriter.lazyEq.cacheEqConstraints(nextState, cmdElems.map((_, pickedResult)))

                // We ensure that the pickedResult is in cdm. Correctness of the domain is ensured by the for-loop
                // inAndEq checks if pickedResult is in cdm
                val elemsInAndEq = cmdElems.map(inAndEq(rewriter, _, pickedResult, cdm, lazyEq = true))
                rewriter.solverContext.assertGroundExpr(tla.or(elemsInAndEq: _*))
              } else {
                rewriter.solverContext.assertGroundExpr(tla.selectInSet(pickedResult.toBuilder, cdm.toBuilder))
              }
          }

        case SMTEncoding.OOPSLA19 =>
          nextState = nextState.updateArena(_.appendHas(pair, arg, SmtConstElemPtr(pickedResult)))
          nextState = nextState.updateArena(_.appendHas(relationCell, SmtConstElemPtr(pair)))
          val ite = tla.ite(isNonDup.toBuilder, tla.storeInSet(pair.toBuilder, relationCell.toBuilder),
              tla.storeNotInSet(pair.toBuilder, relationCell.toBuilder))
          rewriter.solverContext.assertGroundExpr(ite)

        case oddEncodingType =>
          throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
      }
    }

    // If S is empty, the relation is empty too.

    rewriter.solverContext.log("; } PICK %s FROM %s".format(funT, funSet))
    nextState.setRex(funCell.toBuilder)
  }

  // just declare an integer, and in case of Nat make it non-negative
  def pickFromIntOrNatSet(set: ArenaCell, state: SymbState): SymbState = {
    assert(set == state.arena.cellNatSet() || set == state.arena.cellIntSet())
    val nextState = state.updateArena(_.appendCell(IntT1))
    val intCell = nextState.arena.topCell
    if (set == state.arena.cellNatSet()) {
      rewriter.solverContext.assertGroundExpr(tla.ge(intCell.toBuilder, tla.int(0)))
    }
    nextState.setRex(intCell.toBuilder)
  }
}
