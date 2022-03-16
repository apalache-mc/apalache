package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.{MalformedSepecificationError, OperEx, SeqT1, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.oper.TlaOper

import scala.collection.immutable.SortedMap
import at.forsyte.apalache.tla.typecheck.ModelValueHandler
import scalaz.unused

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
  def pick(set: ArenaCell, state: SymbState, elseAssert: TlaEx): SymbState = {
    set.cellType match {
      // all kinds of sets that should be kept unexpanded
      case PowSetT(t @ FinSetT(_)) =>
        // a powerset is never empty, pick an element
        pickFromPowset(t, set, state)

      case FinFunSetT(domt @ FinSetT(_), FinSetT(rest)) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT(domt, rest), set, state)

      case FinFunSetT(domt @ FinSetT(_), InfSetT(rest)) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT(domt, rest), set, state)

      case FinFunSetT(domt @ FinSetT(_), PowSetT(resultT @ FinSetT(_))) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT(domt, resultT), set, state)

      case FinFunSetT(dom1T @ FinSetT(_), FinFunSetT(dom2T @ FinSetT(_), FinSetT(result2T))) =>
        pickFunFromFunSet(FunT(dom1T, FunT(dom2T, result2T)), set, state)

      case FinFunSetT(dom1T @ FinSetT(_), FinFunSetT(dom2T @ FinSetT(_), PowSetT(result2T @ FinSetT(_)))) =>
        pickFunFromFunSet(FunT(dom1T, FunT(dom2T, result2T)), set, state)

      case FinFunSetT(FinSetT(_), PowSetT(_)) | FinFunSetT(FinSetT(_), FinFunSetT(_, _)) =>
        throw new RewriterException(s"Rewriting for the type ${set.cellType} is not implemented. Raise an issue.",
            state.ex)

      case InfSetT(IntT()) if set == state.arena.cellIntSet() || set == state.arena.cellNatSet() =>
        // pick an integer or natural
        pickFromIntOrNatSet(set, state)

      case _ =>
        val elems = state.arena.getHas(set)
        if (elems.isEmpty) {
          throw new RuntimeException(s"The set $set is statically empty. Pick should not be called on that.")
        }

        var (nextState, oracle) = oracleFactory.newDefaultOracle(state, elems.size + 1)

        // pick only the elements that belong to the set
        val elemsIn = elems.map { c => tla.apalacheSelectInSet(c.toNameEx, set.toNameEx).untyped() }
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
      elseAssert: TlaEx): SymbState = {
    assert(elems.nonEmpty) // this is an advanced operator -- you should know what you are doing
    val targetType = elems.head.cellType

    // An optimization: if the (multi-) set consists of identical cells, return the cell
    // (e.g., this happens when all enabled transitions do not change a variable.)
    if (elems.distinct.size == 1) {
      return state.setRex(elems.head.toNameEx)
    }

    // the general case
    targetType match {
      case ConstT(x) =>
        pickBasic(ConstT(x), state, oracle, elems, elseAssert)

      case IntT() =>
        pickBasic(IntT(), state, oracle, elems, elseAssert)

      case BoolT() =>
        pickBasic(BoolT(), state, oracle, elems, elseAssert)

      case t @ TupleT(_) =>
        pickTuple(t, state, oracle, elems, elseAssert)

      case t @ RecordT(_) =>
        pickRecord(t, state, oracle, elems, elseAssert)

      case t @ FinSetT(_) =>
        pickSet(t, state, oracle, elems, elseAssert)

      case t @ SeqT(_) =>
        pickSequence(t, state, oracle, elems, elseAssert)

      case t @ FunT(FinSetT(_), _) =>
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
      cellType: CellT,
      state: SymbState,
      oracle: Oracle,
      elems: Seq[ArenaCell],
      elseAssert: TlaEx): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, elems.map(_.toString).mkString(", ")))
    val arena = state.arena.appendCell(cellType)
    val resultCell = arena.topCell
    // compare the set contents with the result
    val eqState = rewriter.lazyEq.cacheEqConstraints(state, elems.map(e => (e, resultCell)))
    // the new element equals to an existing element in the set
    val asserts = elems.map { el => rewriter.lazyEq.safeEq(resultCell, el) }
    rewriter.solverContext.assertGroundExpr(oracle.caseAssertions(eqState, asserts :+ elseAssert))

    rewriter.solverContext.log(s"; } CHERRY-PICK $resultCell:$cellType")
    eqState.setArena(arena).setRex(resultCell.toNameEx)
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
      cellType: CellT,
      state: SymbState,
      oracle: Oracle,
      tuples: Seq[ArenaCell],
      elseAssert: TlaEx): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, tuples.map(_.toString).mkString(", ")))
    val tupleType = cellType.asInstanceOf[TupleT]

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
    val newFields = tupleType.args.indices.map(pickAtPos)

    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element t[i], as it will use the same oracle!

    // add the new fields to arena
    val newArena = newState.arena.appendHasNoSmt(newTuple, newFields: _*)
    rewriter.solverContext.log(s"; } CHERRY-PICK $newTuple:$cellType")
    newState
      .setArena(newArena)
      .setRex(newTuple.toNameEx)

  }

  /**
   * Implements SE-PICK-RECORD.
   *
   * Note that some record fields may have bogus values, since not all the records in the set are required to have all
   * the keys assigned. That is an unavoidable loophole in the record types.
   *
   * @param cellTypeToIgnore
   *   a cell type to assign to the picked cell, this is not always the right type for records
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
      @unused cellTypeToIgnore: CellT,
      state: SymbState,
      oracle: Oracle,
      records: Seq[ArenaCell],
      elseAssert: TlaEx): SymbState = {
    // the records do not always have the same type, but they do have compatible types
    val commonRecordT = findCommonRecordType(records)
    rewriter.solverContext
      .log("; CHERRY-PICK %s FROM [%s] {".format(commonRecordT, records.map(_.toString).mkString(", ")))

    def findKeyIndex(recT: RecordT, key: String): Int =
      recT.fields.keySet.toList.indexOf(key)

    var newState = state

    def getKeyOrDefault(record: ArenaCell, key: String): ArenaCell = {
      val thisRecT = record.cellType.asInstanceOf[RecordT]
      if (thisRecT.fields.contains(key)) {
        val keyIndex = findKeyIndex(thisRecT, key)
        val edges = newState.arena.getHas(record)
        try {
          edges(keyIndex)
        } catch {
          case _: IndexOutOfBoundsException =>
            // TODO Remove once sound record typing is implemented
            val url =
              "https://apalache.informal.systems/docs/apalache/known-issues.html#updating-records-with-excess-fields"
            val msg = s"""|An updated record has more fields than its declared type:
                          |A record with the inferred type `${thisRecT.toTlaType1}` has been updated with
                          |the key `${key}` in an `EXCEPT` expression and the updated record has more fields
                          |than are specified in its type annotation. For details see $url""".stripMargin.linesIterator
              .mkString(" ")
              .trim
            throw new MalformedSepecificationError(msg)
        }
      } else {
        // This record does not have the key, but it was mixed with other records and produced a more general type.
        // Return a default value. As we are iterating over fields of commonRecordT, we will always find a value.
        val valueT = commonRecordT.fields(key)
        val (newArena, defaultValue) = rewriter.defaultValueCache.getOrCreate(newState.arena, valueT.toTlaType1)
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
    newState = pickRecordDomain(commonRecordT, FinSetT(ConstT()), newState, oracle,
        records.map(r => newState.arena.getDom(r)))
    val newDom = newState.asCell
    // pick the fields using the oracle
    val fieldCells = commonRecordT.fields.keySet.toSeq.map(pickAtPos)
    // and connect them to the record
    var newArena = newState.arena.setDom(newRecord, newDom)
    newArena = newArena.appendHasNoSmt(newRecord, fieldCells: _*)
    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element r.key, as it will use the same oracle!

    rewriter.solverContext.log(s"; } CHERRY-PICK $newRecord:$commonRecordT")

    newState
      .setArena(newArena)
      .setRex(newRecord.toNameEx)
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
      commonRecordType: RecordT,
      domType: CellT,
      state: SymbState,
      oracle: Oracle,
      domains: Seq[ArenaCell]): SymbState = {
    // It often happens that all the domains are actually the same cell. Return this cell.
    val distinct = domains.distinct
    if (distinct.size == 1) {
      state.setRex(distinct.head.toNameEx)
    } else {
      val (newState, keyToCell) = findRecordKeys(state, commonRecordType)
      // Introduce a new cell for the picked domain
      var nextState = newState.updateArena(_.appendCell(domType))
      val newDom = nextState.arena.topCell
      // Add the cells for all potential keys.
      // Importantly, they all come from strValueCache, so the same key produces the same cell.
      val keyCells = keyToCell.values.toSeq
      nextState = nextState.updateArena(_.appendHas(newDom, keyCells: _*))
      // Constrain membership with SMT
      for ((dom, no) <- domains.zipWithIndex) {
        val domainCells = nextState.arena.getHas(dom)

        for (keyCell <- keyCells) {
          // Although we search over a list, the list size is usually small, e.g., up to 10 elements
          if (domainCells.contains(keyCell)) {
            // The key belongs to the new domain only if it belongs to the domain that is pointed by the oracle
            val ite = tla.ite(tla.apalacheSelectInSet(keyCell.toNameEx, dom.toNameEx),
                tla.apalacheStoreInSet(keyCell.toNameEx, newDom.toNameEx),
                tla.apalacheStoreNotInSet(keyCell.toNameEx, newDom.toNameEx))
            val unchangedSet = rewriter.solverContext.config.smtEncoding match {
              case `arraysEncoding` =>
                // In the arrays encoding we need to propagate the SSA representation of the array if nothing changes
                tla.apalacheStoreNotInSet(keyCell.toNameEx, newDom.toNameEx)
              case `oopsla19Encoding` =>
                tla.bool(true)
              case oddEncodingType =>
                throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
            }
            rewriter.solverContext.assertGroundExpr(tla.ite(oracle.whenEqualTo(nextState, no), ite, unchangedSet))
          } else {
            // The domain pointed by the oracle does not contain the key
            val notInDom = tla.not(tla.apalacheSelectInSet(keyCell.toNameEx, newDom.toNameEx))
            rewriter.solverContext.assertGroundExpr(tla.impl(oracle.whenEqualTo(nextState, no), notInDom))
          }
        }
      }
      nextState.setRex(newDom.toNameEx)
    }
  }

  private def findCommonRecordType(records: Seq[ArenaCell]): RecordT = {
    var maxRecordType = records.head.cellType
    for (rec <- records.tail) {
      val recType = rec.cellType
      recType.unify(maxRecordType) match {
        case Some(commonType) =>
          maxRecordType = commonType

        case None =>
          throw new IllegalStateException(s"Found inconsistent records in a set: $maxRecordType and $recType")
      }
    }
    maxRecordType.asInstanceOf[RecordT]
  }

  // find the union of the keys for all records, if it exists
  private def findRecordKeys(state: SymbState, recordType: RecordT): (SymbState, SortedMap[String, ArenaCell]) = {
    val commonKeys = recordType.asInstanceOf[RecordT].fields.keySet
    var keyToCell = SortedMap[String, ArenaCell]()
    var nextState = state
    for (key <- commonKeys) {
      val (newArena, cell) = rewriter.modelValueCache.getOrCreate(nextState.arena, (ModelValueHandler.STRING_TYPE, key))
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
      cellType: CellT,
      state: SymbState,
      oracle: Oracle,
      memberSets: Seq[ArenaCell],
      elseAssert: TlaEx,
      noSmt: Boolean = false): SymbState = {
    if (memberSets.isEmpty) {
      throw new RuntimeException("Picking from a statically empty set")
    } else if (memberSets.length == 1) {
      // one set, either empty, or not
      state.setRex(memberSets.head.toNameEx)
    } else if (memberSets.distinct.length == 1) {
      // all sets are actually the same, this is quite common for function domains
      state.setRex(memberSets.head.toNameEx)
    } else if (memberSets.forall(ms => state.arena.getHas(ms).isEmpty)) {
      // multiple sets that are statically empty, just pick the first one
      state.setRex(memberSets.head.toNameEx)
    } else {
      pickSetNonEmpty(cellType, state, oracle, memberSets, elseAssert, noSmt)
    }
  }

  private def pickSetNonEmpty(
      cellType: CellT,
      state: SymbState,
      oracle: Oracle,
      memberSets: Seq[ArenaCell],
      elseAssert: TlaEx,
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
      def nthIn(elemAndSet: (ArenaCell, ArenaCell), no: Int): (TlaEx, TlaEx) = {
        if (elemsOfMemberSets(no).nonEmpty) {
          val inSet = tla.ite(tla.apalacheSelectInSet(elemAndSet._1.toNameEx, elemAndSet._2.toNameEx),
              tla.apalacheStoreInSet(picked.toNameEx, resultCell.toNameEx),
              tla.apalacheStoreNotInSet(picked.toNameEx, resultCell.toNameEx))
          val unchangedSet = rewriter.solverContext.config.smtEncoding match {
            case `arraysEncoding` =>
              // In the arrays encoding we need to propagate the SSA representation of the array if nothing changes
              tla.apalacheStoreNotInSet(picked.toNameEx, resultCell.toNameEx)
            case `oopsla19Encoding` =>
              tla.bool(true)
            case oddEncodingType =>
              throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
          }
          (inSet, unchangedSet)
        } else {
          // nothing belongs to the set
          (tla.apalacheStoreNotInSet(picked.toNameEx, resultCell.toNameEx), tla.bool(true))
        }
      }

      // add the cell to the arena
      nextState = nextState.updateArena(_.appendHas(resultCell, picked))
      if (!noSMT) { // add the SMT constraints
        val assertions = (toPickFrom.zip(memberSets).zipWithIndex.map((nthIn _).tupled)).unzip
        // (chosen = 1 /\ in(z_i, R) = in(c_i, S_1)) \/ (chosen = 2 /\ in(z_i, R) = in(d_i, S_2))
        val membershipAssertions = assertions._1
        val nonMembershipAssertions = assertions._2
        solverAssert(oracle.caseAssertions(nextState, membershipAssertions :+ elseAssert,
                nonMembershipAssertions :+ ValEx(TlaBool(true))))
      }
    }

    0.until(maxLen).foreach(pickOneElement)

    rewriter.solverContext.log(s"; } CHERRY-PICK $resultCell:$cellType")
    nextState.setRex(resultCell.toNameEx)
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
      cellType: CellT,
      state: SymbState,
      oracle: Oracle,
      memberSeqs: Seq[ArenaCell],
      elseAssert: TlaEx): SymbState = {
    if (memberSeqs.isEmpty) {
      throw new RuntimeException("Picking a sequence from a statically empty set")
    } else if (memberSeqs.length == 1) {
      // one sequence, either empty, or not
      state.setRex(memberSeqs.head.toNameEx)
    } else if (memberSeqs.distinct.length == 1) {
      // all sequences are actually the same cell
      state.setRex(memberSeqs.head.toNameEx)
    } else if (memberSeqs.forall(ms => protoSeqOps.unpackSeq(state.arena, ms)._3 == 0)) {
      // multiple sequences that have capacity of 0
      state.setRex(memberSeqs.head.toNameEx)
    } else {
      pickSequenceNonEmpty(cellType, state, oracle, memberSeqs, elseAssert)
    }
  }

  // Pick from a sequences of sequences
  private def pickSequenceNonEmpty(
      seqType: CellT,
      state: SymbState,
      oracle: Oracle,
      memberSeqs: Seq[ArenaCell],
      elseAssert: TlaEx): SymbState = {
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
      rewriter.defaultValueCache.getOrCreate(state.arena, seqType.toTlaType1.asInstanceOf[SeqT1].elem)
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
    nextState = pickBasic(IntT(), nextState, oracle, memberLengths, elseAssert)
    val length = nextState.asCell
    // construct the sequence
    nextState = protoSeqOps.mkSeq(nextState, seqType.toTlaType1, protoSeq, length)

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
      funType: FunT,
      state: SymbState,
      oracle: Oracle,
      funs: Seq[ArenaCell],
      elseAssert: TlaEx): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(funType, funs.map(_.toString).mkString(", ")))
    var nextState = state
    rewriter.solverContext.config.smtEncoding match {
      case `arraysEncoding` =>
        // We create an unconstrained SMT array that can be equated to the cells of funs for the oracle assertions
        nextState = nextState.updateArena(_.appendCell(funType, isUnconstrained = true))
        val funCell = nextState.arena.topCell

        // Pick a function in funs and generate a SMT equality between it and funCell
        val asserts = funs.map { el => OperEx(TlaOper.eq, funCell.toNameEx, el.toNameEx) }
        rewriter.solverContext.assertGroundExpr(oracle.caseAssertions(nextState, asserts :+ elseAssert))

        // Propagate the picked function's domain, by relying on the same oracle used to pick the function
        val domT = FinSetT(funType.argType)
        nextState = pickSet(domT, nextState, oracle, funs.map(nextState.arena.getDom), elseAssert)
        val pickedDom = nextState.asCell
        nextState = nextState.updateArena(_.setDom(funCell, pickedDom))

        // Propagate the picked function's relation, by relying on the same oracle used to pick the function
        val relationT = FinSetT(TupleT(Seq(funType.argType, funType.resultType)))
        nextState = pickSet(relationT, nextState, oracle, funs.map(nextState.arena.getCdm), elseAssert, noSmt = true)
        val pickedRelation = nextState.asCell
        nextState = nextState.updateArena(_.setCdm(funCell, pickedRelation))

        rewriter.solverContext.log(s"; } CHERRY-PICK $funCell:$funType")
        // That's it!
        nextState.setRex(funCell.toNameEx)

      case `oopsla19Encoding` =>
        // Pick the relation
        val relationT = FinSetT(TupleT(Seq(funType.argType, funType.resultType)))
        nextState = pickSet(relationT, nextState, oracle, funs.map(nextState.arena.getCdm), elseAssert)
        val pickedRelation = nextState.asCell
        // Create a fresh cell to hold the function
        nextState = nextState.setArena(nextState.arena.appendCell(funType))
        val funCell = nextState.arena.topCell
        val newArena = nextState.arena.setCdm(funCell, pickedRelation)
        rewriter.solverContext.log(s"; } CHERRY-PICK $funCell:$funType")
        // That's it!
        nextState.setArena(newArena).setRex(funCell.toNameEx)

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
    nextState = nextState.updateArena(_.appendCell(resultType))
    val resultSet = nextState.arena.topCell
    val baseSet = nextState.arena.getDom(set)
    val elems = nextState.arena.getHas(baseSet)
    // resultSet may contain all the elements from the baseSet of the powerset SUBSET(S)
    nextState = nextState.updateArena(_.appendHas(resultSet, elems: _*))

    // if resultSet has an element, then it must be also in baseSet
    def inResultIfInBase(elem: ArenaCell): Unit = {
      // In the oopsla19 encoding resultSet is initially unconstrained, and thus can contain any combination of elems.
      // To emulate this in the arrays encoding, in which the all sets are initially empty, unconstrained predicates
      // are used to allow the SMT solver to consider all possible combinations of elems.
      if (rewriter.solverContext.config.smtEncoding == arraysEncoding) {
        nextState = nextState.updateArena(_.appendCell(BoolT()))
        val pred = nextState.arena.topCell.toNameEx
        val storeElem = tla.apalacheStoreInSet(elem.toNameEx, resultSet.toNameEx)
        val notStoreElem = tla.apalacheStoreNotInSet(elem.toNameEx, resultSet.toNameEx)
        rewriter.solverContext.assertGroundExpr(tla.ite(pred, storeElem, notStoreElem))
      }

      val inResult = tla.apalacheSelectInSet(elem.toNameEx, resultSet.toNameEx)
      val inBase = tla.apalacheSelectInSet(elem.toNameEx, baseSet.toNameEx)
      rewriter.solverContext.assertGroundExpr(tla.impl(inResult, inBase))
    }

    elems.foreach(inResultIfInBase)
    rewriter.solverContext.log("; } PICK %s FROM %s".format(resultType, set))
    nextState.setRex(resultSet.toNameEx)
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
  def pickFunFromFunSet(funT: CellT, funSet: ArenaCell, state: SymbState): SymbState = {
    rewriter.solverContext.log("; PICK %s FROM %s {".format(funT, funSet))
    var arena = state.arena
    val dom = arena.getDom(funSet) // this is a set of potential arguments, always expanded!
    val cdm = arena.getCdm(funSet) // this is a set of potential results, may be expanded, may be not.
    // TODO: take care of [S -> {}], what is the semantics of it?
    val funType = funT.asInstanceOf[FunT] // for now, only FunT is supported
    // create the unconstrained function cell
    arena = arena.appendCell(funT, isUnconstrained = true)
    val funCell = arena.topCell
    // create the relation cell
    arena = arena.appendCell(FinSetT(TupleT(Seq(funType.argType, funType.resultType))))
    val relationCell = arena.topCell
    arena = arena.setDom(funCell, dom)
    arena = arena.setCdm(funCell, relationCell)
    var nextState = state.setArena(arena)

    // For every domain cell, pick a result from the co-domain.
    // The beauty of CherryPick: when the co-domain is not expanded, CherryPick will pick one value out of the co-domain,
    // instead of constructing the co-domain first.
    for (arg <- arena.getHas(dom)) {
      nextState = pick(cdm, nextState, nextState.arena.cellFalse().toNameEx) // the co-domain should be non-empty
      val pickedResult = nextState.asCell

      nextState = nextState.updateArena(_.appendCell(TupleT(Seq(funType.argType, funType.resultType))))
      val pair = nextState.arena.topCell
      nextState = nextState.updateArena(_.appendHasNoSmt(pair, arg, pickedResult))

      rewriter.solverContext.config.smtEncoding match {
        case `arraysEncoding` =>
          nextState = nextState.updateArena(_.appendHasNoSmt(relationCell, pair)) // We only carry the metadata here
          // Since relationCell was updated above with the pair for the current arg, we can use appFun now
          nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.appFun(funCell.toNameEx, arg.toNameEx)))
          val appFunRes = nextState.asCell

          cdm.cellType match {
            case _: PowSetT =>
              val powSetDom = nextState.arena.getDom(cdm)
              val appFunResInDom = tla.subseteq(powSetDom.toNameEx, appFunRes.toNameEx)
              nextState = rewriter.rewriteUntilDone(nextState.setRex(appFunResInDom))
              val resCell = nextState.asCell
              rewriter.solverContext.assertGroundExpr(resCell.toNameEx)

            case _: FinFunSetT =>
              nextState = pick(cdm, nextState, nextState.arena.cellFalse().toNameEx)
              val recursivelyPickedFun = nextState.asCell
              rewriter.solverContext.assertGroundExpr(tla.eql(appFunRes.toNameEx, recursivelyPickedFun.toNameEx))

            case _: InfSetT =>
              nextState = nextState.updateArena(_.appendCell(cdm.cellType.asInstanceOf[InfSetT].elemType))
              val unboundElem = nextState.asCell
              val eql = tla.eql(appFunRes.toNameEx, unboundElem.toNameEx)
              val ge = tla.ge(unboundElem.toNameEx, ValEx(TlaInt(0)))
              rewriter.solverContext.assertGroundExpr(eql)
              if (cdm == state.arena.cellNatSet()) rewriter.solverContext.assertGroundExpr(ge) // Add Nat constraint

            case _ =>
              rewriter.solverContext.assertGroundExpr(tla.apalacheSelectInFun(appFunRes.toNameEx, cdm.toNameEx))
          }

        case `oopsla19Encoding` =>
          nextState = nextState.updateArena(_.appendHas(relationCell, pair))
          val ite = tla.ite(tla.apalacheSelectInSet(arg.toNameEx, dom.toNameEx),
              tla.apalacheStoreInSet(pair.toNameEx, relationCell.toNameEx),
              tla.apalacheStoreNotInSet(pair.toNameEx, relationCell.toNameEx))
          rewriter.solverContext.assertGroundExpr(ite)

        case oddEncodingType =>
          throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
      }
    }

    // If S is empty, the relation is empty too.

    rewriter.solverContext.log("; } PICK %s FROM %s".format(funT, funSet))
    nextState.setRex(funCell.toNameEx)
  }

  // just declare an integer, and in case of Nat make it non-negative
  def pickFromIntOrNatSet(set: ArenaCell, state: SymbState): SymbState = {
    assert(set == state.arena.cellNatSet() || set == state.arena.cellIntSet())
    val nextState = state.updateArena(_.appendCell(IntT()))
    val intCell = nextState.arena.topCell
    if (set == state.arena.cellNatSet()) {
      rewriter.solverContext.assertGroundExpr(tla.ge(intCell.toNameEx, tla.int(0)))
    }
    nextState.setRex(intCell.toNameEx)
  }
}
