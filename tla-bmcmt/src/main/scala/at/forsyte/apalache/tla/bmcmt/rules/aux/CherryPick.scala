package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.{NameEx, NullEx, TlaEx, ValEx}

/**
  * An element picket that allows us:
  *
  * <ul>
  * <li>to pick from a list of cells instead of a set, and</li>
  * <li>directly uses a choice oracle to avoid multiple comparisons.</li>
  * </ul>
  *
  * @param rewriter a state rewriter
  * @author Igor Konnov
  */
class CherryPick(rewriter: SymbStateRewriter) {
  private val defaultValueFactory = new DefaultValueFactory(rewriter)
  val oracleFactory = new OracleFactory(rewriter)

  /**
    * Determine the type of the set elements an element of this type by introducing an oracle
    *
    * @param set   a set
    * @param state a symbolic state
    * @param elseAssert an assertion that is used when the set is empty
    * @return a new symbolic state whose expression stores a fresh cell that corresponds to the picked element.
    */
  def pick(set: ArenaCell, state: SymbState, elseAssert: TlaEx): SymbState = {
    set.cellType match {
      // all kinds of sets that should be kept unexpanded
      case PowSetT(t@FinSetT(_)) =>
        // a powerset is never empty, pick an element
        pickFromPowset(t, set, state)

      case FinFunSetT(domt@FinSetT(_), cdm@FinSetT(rest)) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT(domt, rest), set, state)

      case FinFunSetT(domt@FinSetT(_), cdm@PowSetT(resultT @ FinSetT(_))) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT(domt, resultT), set, state)

      case FinFunSetT(dom1T@FinSetT(_), FinFunSetT(dom2T @ FinSetT(_), FinSetT(result2T))) =>
        pickFunFromFunSet(FunT(dom1T, FunT(dom2T, result2T)), set, state)

      case FinFunSetT(dom1T@FinSetT(_), cdm @ FinFunSetT(dom2T @ FinSetT(_), PowSetT(result2T @ FinSetT(_)))) =>
        pickFunFromFunSet(FunT(dom1T, FunT(dom2T, result2T)), set, state)

      case FinFunSetT(FinSetT(_), PowSetT(_)) | FinFunSetT(FinSetT(_), FinFunSetT(_, _)) =>
        throw new RewriterException(s"Rewriting for the type ${set.cellType} is not implemented. Raise an issue.", state.ex)

      case InfSetT(IntT()) if set == state.arena.cellIntSet() || set == state.arena.cellNatSet() =>
        // not really a finite set, but we can pick a value from it
        pickFromIntOrNatSet(set, state)

      case _ =>
        val elems = state.arena.getHas(set)
        if (elems.isEmpty) {
          throw new RuntimeException(s"The set $set is statically empty. Pick should not be called on that.")
        }

        var (nextState, oracle) = oracleFactory.newDefaultOracle(state, elems.size + 1)

        // pick only the elements that belong to the set
        val elemsIn = elems map { tla.in(_, set) }
        rewriter.solverContext.assertGroundExpr(oracle.caseAssertions(nextState, elemsIn :+ elseAssert))

        pickByOracle(nextState, oracle, elems, elseAssert)
    }
  }

  /**
    * Determine the type of the set elements and pick an element of this type.
    *
    * Warning: this method does not check, whether the picked element actually belongs to the set.
    * You have to do it yourself.
    *
    * @param state  a symbolic state
    * @param oracle a variable that stores which element (by index) should be picked, can be unrestricted
    * @param elems  a non-empty set of cells
    * @return a new symbolic state whose expression stores a fresh cell that corresponds to the picked element.
    */
  def pickByOracle(state: SymbState, oracle: Oracle, elems: Seq[ArenaCell], elseAssert: TlaEx): SymbState = {
    assert(elems.nonEmpty) // this is an advanced operator -- you should know what you are doing
    val targetType = elems.head.cellType

    // An optimization: if the (multi-) set consists of identical cells, return the cell
    // (e.g., this happens when all enabled transitions do not change a variable.)
    if (elems.distinct.size == 1) {
      return state.setRex(elems.head)
    }

    // the general case
    targetType match {
      case ConstT() =>
        pickBasic(ConstT(), state, oracle, elems, elseAssert)

      case IntT() =>
        pickBasic(IntT(), state, oracle, elems, elseAssert)

      case BoolT() =>
        pickBasic(BoolT(), state, oracle, elems, elseAssert)

      case t@TupleT(_) =>
        pickTuple(t, state, oracle, elems, elseAssert)

      case t@RecordT(_) =>
        pickRecord(t, state, oracle, elems, elseAssert)

      case t@FinSetT(_) =>
        pickSet(t, state, oracle, elems, elseAssert)

      case t@SeqT(_) =>
        pickSequence(t, state, oracle, elems, elseAssert)

      case t@FunT(FinSetT(_), _) =>
        pickFun(t, state, oracle, elems, elseAssert)

      case _ =>
        throw new RewriterException("Do not know how pick an element from a set of type: " + targetType, state.ex)
    }
  }


  /**
    * Pick a basic value, that is, an integer, Boolean, or constant.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param state    a symbolic state
    * @param oracle   a variable that stores which element (by index) should be picked, can be unrestricted
    * @param elems    a sequence of elements of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickBasic(cellType: CellT, state: SymbState, oracle: Oracle,
                elems: Seq[ArenaCell], elseAssert: TlaEx): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, elems.map(_.toString).mkString(", ")))
    var arena = state.arena.appendCell(cellType)
    val resultCell = arena.topCell
    // compare the set contents with the result
    val eqState = rewriter.lazyEq.cacheEqConstraints(state, elems.map(e => (e, resultCell)))
    // the new element equals to an existing element in the set
    val asserts = elems map { el => rewriter.lazyEq.safeEq(resultCell, el) }
    rewriter.solverContext.assertGroundExpr(oracle.caseAssertions(eqState, asserts :+ elseAssert))

    rewriter.solverContext.log(s"; } CHERRY-PICK $resultCell:$cellType")
    eqState.setArena(arena).setRex(resultCell)
  }

  /**
    * Implements SE-PICK-TUPLE.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param state    a symbolic state
    * @param oracle   a variable that stores which element (by index) should be picked, can be unrestricted
    * @param tuples   a sequence of records of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickTuple(cellType: CellT, state: SymbState, oracle: Oracle,
                tuples: Seq[ArenaCell], elseAssert: TlaEx): SymbState = {
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
    val newFields = tupleType.args.indices map pickAtPos

    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element t[i], as it will use the same oracle!

    // add the new fields to arena
    val newArena = newState.arena.appendHasNoSmt(newTuple, newFields: _*)
    rewriter.solverContext.log(s"; } CHERRY-PICK $newTuple:$cellType")
    newState
      .setArena(newArena)
      .setRex(newTuple.toNameEx)
      .setTheory(CellTheory())
  }

  /**
    * Implements SE-PICK-RECORD.
    *
    * Note that some record fields may have bogus values, since not all the records in the set
    * are required to have all the keys assigned. That is an unavoidable loophole in the record types.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param state    a symbolic state
    * @param oracle   a variable that stores which element (by index) should be picked, can be unrestricted
    * @param records  a sequence of records of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickRecord(cellType: CellT, state: SymbState, oracle: Oracle,
                 records: Seq[ArenaCell], elseAssert: TlaEx): SymbState = {
    // since we require all records to have exactly the same type, the code became much simpler
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, records.map(_.toString).mkString(", ")))
    val recordType = cellType.asInstanceOf[RecordT]

    def findKeyIndex(key: String): Int =
      recordType.fields.keySet.toList.indexOf(key)

    var newState = state

    def pickAtPos(key: String): ArenaCell = {
      val keyIndex = findKeyIndex(key)
      val slice = records.map(c => newState.arena.getHas(c)(keyIndex))
      newState = pickByOracle(newState, oracle, slice, elseAssert)
      newState.asCell
    }

    // introduce a new record
    newState = newState.setArena(newState.arena.appendCell(cellType))
    val newRecord = newState.arena.topCell
    // pick the domain using the oracle.
//    newState = pickSet(FinSetT(ConstT()), newState, oracle, records map (r => newState.arena.getDom(r)))
    newState = pickRecordDomain(FinSetT(ConstT()), newState, oracle, records map (r => newState.arena.getDom(r)))
    val newDom = newState.asCell
    // pick the fields using the oracle
    val fieldCells = recordType.fields.keySet.toSeq map pickAtPos
    // and connect them to the record
    var newArena = newState.arena.setDom(newRecord, newDom)
    newArena = newArena.appendHasNoSmt(newRecord, fieldCells: _*)
    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element r.key, as it will use the same oracle!

    rewriter.solverContext.log(s"; } CHERRY-PICK $newRecord:$cellType")

    newState.setArena(newArena)
      .setTheory(CellTheory())
      .setRex(newRecord.toNameEx)
  }

  /**
    * Pick a set among a sequence of record domains. We know that the types of all the domains are compatible.
    * Moreover, from the record constructor, we know that the record domains have  exactly the same sequence
    * of keys in the arena. Hence, we only have to define the SMT constraints that regulate which keys belong to the new set.
    * This optimization prevents the model checker from blowing up in the number of record domains, e.g., in Raft.
    *
    * @param domType the goal type
    * @param state a symbolic state
    * @param oracle the oracle to use
    * @param domains the domains to pick from
    * @return a new cell that encodes a picked domain
    */
  private def pickRecordDomain(domType: CellT, state: SymbState, oracle: Oracle, domains: Seq[ArenaCell]): SymbState = {
    // TODO: use elseAssert and Oracle.caseAssertions?
    // It often happens that all the domains are actually the same cell. Return this cell.
    val distinct = domains.distinct
    if (distinct.size == 1) {
      state.setRex(distinct.head)
    } else {
      // consistency check: make sure that all the domains consist of exactly the same sets of keys
      val keyCells = state.arena.getHas(domains.head)
      for (dom <- domains.tail) {
        val otherKeyCells = state.arena.getHas(dom)
        assert(otherKeyCells.size == keyCells.size,
          "inconsistent record domains of size %d and %d".format(keyCells.size, otherKeyCells.size))
        for ((k, o) <- keyCells.zip(otherKeyCells)) {
          assert(k == o, s"inconsistent record domains: $k != $o")
        }
      }
      // introduce a new cell for the picked domain
      var nextState = state.updateArena(_.appendCell(domType))
      val newDom = nextState.arena.topCell
      nextState = nextState.updateArena(_.appendHas(newDom, keyCells: _*))
      // once we know that all the keys coincide, constrain membership with SMT
      for ((dom, no) <- domains.zipWithIndex) {
        def iffKey(keyCell: ArenaCell) = tla.equiv(tla.in(keyCell, newDom), tla.in(keyCell, dom))

        val keysMatch = tla.and(keyCells map iffKey: _*)
        rewriter.solverContext.assertGroundExpr(tla.impl(oracle.whenEqualTo(nextState, no), keysMatch))
      }
      nextState.setRex(newDom).setTheory(CellTheory())
    }
  }

  /**
    * Implements SE-PICK-SET.
    *
    * Note that some record fields may have bogus values, since not all the records in the set
    * are required to have all the keys assigned. That is an unavoidable loophole in the record types.
    *
    * @param cellType   a cell type to assign to the picked cell.
    * @param state      a symbolic state
    * @param oracle     a variable that stores which element (by index) should be picked, can be unrestricted
    * @param memberSets a sequence of sets of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickSet(cellType: CellT, state: SymbState, oracle: Oracle,
              memberSets: Seq[ArenaCell], elseAssert: TlaEx): SymbState = {
    if (memberSets.isEmpty) {
      throw new RuntimeException("Picking from a statically empty set")
    } else if (memberSets.length == 1) {
      // one set, either empty, or not
      state.setRex(memberSets.head)
    } else if (memberSets.distinct.length == 1) {
      // all sets are actually the same, this is quite common for function domains
      state.setRex(memberSets.head)
    } else if (memberSets.forall(ms => state.arena.getHas(ms).isEmpty)) {
      // multiple sets that are statically empty, just pick the first one
      state.setRex(memberSets.head)
    } else {
      pickSetNonEmpty(cellType, state, oracle, memberSets, elseAssert)
    }
  }

  private def pickSetNonEmpty(cellType: CellT,
                              state: SymbState,
                              oracle: Oracle,
                              memberSets: Seq[ArenaCell],
                              elseAssert: TlaEx): SymbState = {
    def solverAssert(e: TlaEx): Unit = rewriter.solverContext.assertGroundExpr(e)

    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, memberSets.map(_.toString).mkString(", ")))
    var nextState = state
    // introduce a fresh cell for the set
    nextState = nextState.setArena(state.arena.appendCell(cellType))
    val resultCell = nextState.arena.topCell

    // get all the cells pointed by the elements of every member set
    val elemsOfMemberSets: Seq[Seq[ArenaCell]] = memberSets map (s => Set(nextState.arena.getHas(s): _*).toSeq)

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

    val maxLen = elemsOfMemberSets map (_.size) reduce ((i, j) => if (i > j) i else j)
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
      val toPickFrom = paddedOfMemberSets map { _(i) }
      nextState = pickByOracle(nextState, oracle, toPickFrom, elseAssert)
      val picked = nextState.asCell

      // this property is enforced by the oracle magic: chosen = 1 => z_i = c_i /\ chosen = 2 => z_i = d_i

      // The awesome property of the oracle is that we do not have to compare the sets directly!
      // Instead, we compare the oracle values.
      //  (chosen = 1 /\ in(z_i, R) <=> in(c_i, S_1)) \/ (chosen = 2 /\ in(z_i, R) <=> in(d_i, S_2)) \/ (chosen = N <=> elseAssert)
      def nthIn(elemAndSet: (ArenaCell, ArenaCell), no: Int): TlaEx = {
        if (elemsOfMemberSets(no).nonEmpty) {
          tla.equiv(tla.in(picked.toNameEx, resultCell.toNameEx), tla.in(elemAndSet._1, elemAndSet._2))
        } else {
          tla.not(tla.in(picked.toNameEx, resultCell.toNameEx)) // nothing belongs to the set
        }
      }

      val assertions = toPickFrom.zip(memberSets).zipWithIndex map (nthIn _).tupled
      // add the cell to the arena
      nextState = nextState.updateArena(_.appendHas(resultCell, picked))
      // (chosen = 1 /\ in(z_i, R) = in(c_i, S_1)) \/ (chosen = 2 /\ in(z_i, R) = in(d_i, S_2))
      solverAssert(oracle.caseAssertions(nextState, assertions :+ elseAssert))
    }

    0.until(maxLen) foreach pickOneElement

    rewriter.solverContext.log(s"; } CHERRY-PICK $resultCell:$cellType")
    nextState.setRex(resultCell)
  }

  /**
    * Picks a sequence from a list of sequences
    *
    * @param cellType   a cell type to assign to the picked cell.
    * @param state      a symbolic state
    * @param oracle     a variable that stores which element (by index) should be picked, can be unrestricted
    * @param memberSeqs a sequence of sequences of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickSequence(cellType: CellT, state: SymbState, oracle: Oracle,
                   memberSeqs: Seq[ArenaCell], elseAssert: TlaEx): SymbState = {
    if (memberSeqs.isEmpty) {
      throw new RuntimeException("Picking a sequence from a statically empty set")
    } else if (memberSeqs.length == 1) {
      // one sequence, either empty, or not
      state.setRex(memberSeqs.head)
    } else if (memberSeqs.distinct.length == 1) {
      // all sequences are actually the same cell
      state.setRex(memberSeqs.head)
    } else if (memberSeqs.forall(ms => state.arena.getHas(ms).size == 2)) {
      // multiple sequences that are statically empty (note that the first two elements are start and end)
      state.setRex(memberSeqs.head)
    } else if (memberSeqs.forall(ms => state.arena.getHas(ms).isEmpty)) {
      throw new IllegalStateException(s"Corrupted sequences, no start and end: $memberSeqs")
    } else {
      pickSequenceNonEmpty(cellType, state, oracle, memberSeqs, elseAssert)
    }
  }

  // Pick from a set of sequence. There is a large overlap with pickSetNonEmpty
  private def pickSequenceNonEmpty(seqType: CellT,
                                   state: SymbState,
                                   oracle: Oracle,
                                   memberSeqs: Seq[ArenaCell],
                                   elseAssert: TlaEx): SymbState = {
    def solverAssert(e: TlaEx): Unit = rewriter.solverContext.assertGroundExpr(e)

    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(seqType, memberSeqs.map(_.toString).mkString(", ")))
    var nextState = state
    // introduce a fresh cell for the set
    nextState = nextState.setArena(state.arena.appendCell(seqType))
    val resultCell = nextState.arena.topCell

    // get all the cells pointed by the elements of every member set, without changing their order!
    val elemsOfMemberSeqs: Seq[Seq[ArenaCell]] = memberSeqs map (s => nextState.arena.getHas(s).toSeq)

    // Here we are using the awesome linear encoding that uses interleaving.
    // We give an explanation for two statically non-empty sequences, the static case should be handled differently.
    // Assume S_1 = << c_1, ..., c_n >> and S_2 = << d_1, ..., d_n >> (pad if they have different lengths)
    //
    // We construct a new sequence R = << z_1, ..., z_n >> where z_i = FROM { c_i, d_i }
    //
    // As we are not tracking membership for sequences, no additional SMT constraints are needed

    val maxLen = elemsOfMemberSeqs map (_.size) reduce ((i, j) => if (i > j) i else j)
    assert(maxLen != 0)
    val maxPadded = elemsOfMemberSeqs.find(_.size == maxLen).get // there must be one like this

    def padNonEmptySeq(s: Seq[ArenaCell], len: Int): Seq[ArenaCell] = s match {
      // copy the last element as many times as needed
      case allButLast :+ last if allButLast.size >= 2 => // the first two elements are start and end
        allButLast ++ Seq.fill(len - allButLast.length)(last)
      // the empty sequence is a special case
      case start :: end :: Nil => start +: end +: maxPadded.tail.tail // keep the start and end (should be 0 anyhow)
      case _ => throw new IllegalStateException("A corrupted encoding of a sequence")
    }

    val paddedSeqElems = elemsOfMemberSeqs.map(padNonEmptySeq(_, maxLen))
    // no empty sequences beyond this point
    // for each index i, pick from {c_i, ..., d_i}.
    def pickOneElement(i: Int): Unit = {
      val toPickFrom = paddedSeqElems map { _(i) }
      nextState = pickByOracle(nextState, oracle, toPickFrom, elseAssert)
      val picked = nextState.asCell
      // this property is enforced by the oracle magic: chosen = 1 => z_i = c_i /\ chosen = 2 => z_i = d_i
      // add the cell to the arena
      nextState = nextState.updateArena(_.appendHasNoSmt(resultCell, picked))
    }

    0.until(maxLen) foreach pickOneElement

    rewriter.solverContext.log(s"; } CHERRY-PICK $resultCell:$seqType")
    nextState.setRex(resultCell)
  }

  /**
    * This is a new implementation of picking a function from a set. Since we started to encode functions
    * as relations, the implementation became trivial
    *
    * @param funType a cell type to assign to the picked cell.
    * @param oracle  a variable that stores which element (by index) should be picked, can be unrestricted
    * @param funs    a sequence of cells that store functions
    * @param state   a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFun(funType: FunT, state: SymbState, oracle: Oracle, funs: Seq[ArenaCell], elseAssert: TlaEx): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(funType, funs.map(_.toString).mkString(", ")))
    var nextState = state
    // pick the relation
    val relationT = FinSetT(TupleT(Seq(funType.argType, funType.resultType)))
    nextState = pickSet(relationT, nextState, oracle, funs map state.arena.getCdm, elseAssert)
    val pickedRelation = nextState.asCell
    // create a fresh cell to hold the function
    nextState = nextState.setArena(nextState.arena.appendCell(funType))
    val funCell = nextState.arena.topCell
    val newArena = nextState.arena.setCdm(funCell, pickedRelation)
    rewriter.solverContext.log(s"; } CHERRY-PICK $funCell:$funType")
    // That's it! Compare to pickFunPreWarp.
    nextState.setArena(newArena).setRex(funCell).setTheory(CellTheory())
  }

  /**
    * Implements SE-PICK-SET, that is, assume that the picked element is a set itself.
    *
    * @param resultType a cell type to assign to the picked cell.
    * @param set        a powerset
    * @param state      a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFromPowset(resultType: CellT, set: ArenaCell, state: SymbState): SymbState = {
    rewriter.solverContext.log("; PICK %s FROM %s {".format(resultType, set))
    var arena = state.arena.appendCell(resultType)
    val resultSet = arena.topCell
    val baseSet = arena.getDom(set)
    val elems = arena.getHas(baseSet)
    // resultSet may contain all the elements from the baseSet of the powerset SUBSET(S)
    arena = arena.appendHas(resultSet, elems: _*)

    // if resultSet has an element, then it must be also in baseSet
    def inResultIfInBase(elem: ArenaCell): Unit = {
      val inResult = tla.in(elem, resultSet)
      val inBase = tla.in(elem, baseSet)
      rewriter.solverContext.assertGroundExpr(tla.impl(inResult, inBase))
    }

    elems foreach inResultIfInBase
    rewriter.solverContext.log("; } PICK %s FROM %s".format(resultType, set))
    state.setArena(arena).setRex(resultSet)
  }

  /**
    * Picks a function from a set [S -> T].
    * Since [S -> T] is in its unexpanded form, it is easy to pick a function by imposing the constraints
    * from S and T, so we are not using an oracle here. However, we have to take care of T, as it can be
    * an unexpanded set itself, e.g., SUBSET X, or [X -> Y].
    *
    * @param funT   a cell type to assign to the picked cell.
    * @param funSet a function set [S -> T]
    * @param state  a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFunFromFunSet(funT: CellT, funSet: ArenaCell, state: SymbState): SymbState = {
    rewriter.solverContext.log("; PICK %s FROM %s {".format(funT, funSet))
    var arena = state.arena
    val dom = arena.getDom(funSet) // this is a set of potential arguments, always expanded!
    val cdm = arena.getCdm(funSet) // this is a set of potential results, may be expanded, may be not.
    // TODO: take care of [S -> {}], what is the semantics of it?
    val funType = funT.asInstanceOf[FunT] // for now, only FunT is supported
    // create the function cell
    arena = arena.appendCell(funT)
    val funCell = arena.topCell
    // create the relation cell
    arena = arena.appendCell(FinSetT(TupleT(Seq(funType.argType, funType.resultType))))
    val relationCell = arena.topCell
    // not keeping the domain explicitly
    // TODO: why don't we keep the domain? It is always expanded and thus already pre-computed!
//    arena = arena.setDom(funCell, dom)
    arena = arena.setCdm(funCell, relationCell)
    var nextState = state.setArena(arena)

    // For every domain cell, pick a result from the co-domain.
    // The beauty of CherryPick: When the co-domain is not expanded, CherryPick will pick one value out of the co-domain,
    // instead of constructing the co-domain first.
    for (arg <- arena.getHas(dom)) {
      nextState = pick(cdm, nextState, nextState.arena.cellFalse()) // the co-domain should be non-empty
      val pickedResult = nextState.asCell

      arena = nextState.arena.appendCell(TupleT(Seq(funType.argType, funType.resultType)))
      val pair = arena.topCell
      arena = arena.appendHasNoSmt(pair, arg, pickedResult)
      arena = arena.appendHas(relationCell, pair)
      nextState = nextState.setArena(arena)
      val iff = tla.equiv(tla.in(arg, dom), tla.in(pair, relationCell))
      rewriter.solverContext.assertGroundExpr(iff)
    }

    // If S is empty, the relation is empty too.

    rewriter.solverContext.log("; } PICK %s FROM %s".format(funT, funSet))
    nextState.setRex(funCell)
  }

  // just declare an integer, and in case of Nat make it non-negative
  def pickFromIntOrNatSet(set: ArenaCell, state: SymbState): SymbState = {
    assert(set == state.arena.cellNatSet() || set == state.arena.cellIntSet())
    var nextState = state.updateArena(_.appendCell(IntT()))
    val intCell = nextState.arena.topCell
    if (set == state.arena.cellNatSet()) {
      rewriter.solverContext.assertGroundExpr(tla.ge(intCell.toNameEx, tla.int(0)))
    }
    nextState.setRex(intCell).setTheory(CellTheory())
  }
}
