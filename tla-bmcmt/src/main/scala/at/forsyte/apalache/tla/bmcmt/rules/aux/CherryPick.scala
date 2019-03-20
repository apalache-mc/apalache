package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}

/**
  * An advanced form of PickFromAndFunMerge that allows us:
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
  private val picker = new PickFromAndFunMerge(rewriter, failWhenEmpty = false)
  private val defaultValueFactory = new DefaultValueFactory(rewriter)

  /**
    * Determine the type of the set elements an element of this type by introducing an oracle
    *
    * @param set   a set
    * @param state a symbolic state
    * @return a new symbolic state whose expression stores a fresh cell that corresponds to the picked element.
    */
  def pick(set: ArenaCell, state: SymbState): SymbState = {
    set.cellType match {
      case PowSetT(t@FinSetT(_)) =>
        // a powerset is never empty, pick an element
        picker.pickFromPowset(t, set, state)

      case FinFunSetT(domt@FinSetT(_), cdm@FinSetT(rest)) =>
        // No emptiness check, since we are dealing with a function set [S -> T].
        // If S is empty, we get a function of the empty set.
        pickFunFromFunSet(FunT(domt, rest), set, state)

      case _ =>
        val elems = state.arena.getHas(set)
        if (elems.isEmpty) {
          throw new RuntimeException(s"The set $set is statically empty. Pick should not be called on that.")
        }

        var arena = state.arena.appendCell(IntT())
        val oracle = arena.topCell
        val inRange = tla.and(tla.ge(oracle, tla.int(0)), tla.lt(oracle, tla.int(elems.size)))
        rewriter.solverContext.assertGroundExpr(inRange)

        def chooseWhenIn(el: ArenaCell, no: Int): Unit = {
          val chosen = tla.eql(oracle.toNameEx, tla.int(no))
          val in = tla.in(el, set)
          rewriter.solverContext.assertGroundExpr(tla.impl(chosen, in))
        }

        elems.zipWithIndex foreach (chooseWhenIn _).tupled

        pickByOracle(state.setArena(arena), oracle, elems)
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
  def pickByOracle(state: SymbState, oracle: TlaEx, elems: Seq[ArenaCell]): SymbState = {
    assert(elems.nonEmpty) // this is an advanced operator -- you should know what you are doing
    val targetType = elems.head.cellType

    targetType match {
      case ConstT() =>
        pickBasic(ConstT(), state, oracle, elems)

      case IntT() =>
        pickBasic(IntT(), state, oracle, elems)

      case BoolT() =>
        pickBasic(BoolT(), state, oracle, elems)

      case t@TupleT(_) =>
        pickTuple(t, state, oracle, elems)

      case t@RecordT(_) =>
        pickRecord(t, state, oracle, elems)

      case t@FinSetT(_) =>
        pickSet(t, state, oracle, elems)

      case t@SeqT(_) =>
        pickSequence(t, state, oracle, elems)

      case t@FunT(FinSetT(_), _) =>
        pickFun(t, state, oracle, elems)

      case _ =>
        throw new RewriterException("Do not know how pick an element from a set of type: " + targetType)
    }
  }

  /**
    * Intoduce an integer oracle variable over 0..N, where the indices from 0 to N - 1 correspond to the set elements,
    * whereas the index N corresponds to the default choice when the set is empty. This method does not add any
    * constraints on the contents of the set, you can do it by calling constrainOracleWithIn.
    * Nor it defines the default value. It is up to the specific operator how it is done.
    *
    * @param state
    * @param set
    * @param elems
    * @return
    */
  def newOracleWithDefault(state: SymbState, set: ArenaCell, elems: Seq[ArenaCell]): SymbState = {
    // add an oracle \in 0..N, where the indices from 0 to N - 1 correspond to the set elements,
    // whereas the index N corresponds to the default choice when the set is empty
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    val nelems = elems.size
    var nextState = state.setArena(state.arena.appendCell(IntT()))
    val oracle = nextState.arena.topCell.toNameEx
    solverAssert(tla.ge(oracle, tla.int(0)))
    solverAssert(tla.le(oracle, tla.int(nelems)))
    nextState.setRex(oracle).setTheory(CellTheory())
  }

  /**
    * <p>Add the following constraints:</p>
    *
    * <ul>
    *   <li>oracle = i > in(e_i, S) for 0 <= i < N, and</li>
    *   <li>oracle = N => \A i \in 0..(N-1) ~in(e_i, S).</li>
    * </ul>
    *
    * <p>It is often natural to add these constraints. Sometimes, these constraints come in a different form.</p>
    *
    * @param oracle an oracle that is created with newOracleWithDefault
    * @param set a set cell
    * @param setElems the cells pointed by the set
    */
  def constrainOracleWithIn(oracle: ArenaCell, set: ArenaCell, setElems: Seq[ArenaCell]): Unit = {
    def chooseWhenIn(el: ArenaCell, no: Int): Unit = {
      val chosen = tla.eql(oracle.toNameEx, tla.int(no))
      val in = tla.in(el, set)
      rewriter.solverContext.assertGroundExpr(tla.impl(chosen, in))
    }

    // 1. oracle = i > in(e_i, S) for 0 <= i < N
    setElems.zipWithIndex foreach (chooseWhenIn _).tupled
    // 2. oracle = N => \A i \in 0..(N-1) ~in(e_i, S)
    val allNotIn = tla.and(setElems map (e => tla.not(tla.in(e, set))) :_*)
    val defaultChosen = tla.eql(oracle.toNameEx, tla.int(setElems.size))
    rewriter.solverContext.assertGroundExpr(tla.impl(defaultChosen, allNotIn))
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
  def pickBasic(cellType: CellT, state: SymbState, oracle: TlaEx, elems: Seq[ArenaCell]): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, elems.map(_.toString).mkString(", ")))
    var arena = state.arena.appendCell(cellType)
    val resultCell = arena.topCell
    // compare the set contents with the result
    val eqState = rewriter.lazyEq.cacheEqConstraints(state, elems.map(e => (e, resultCell)))

    // the new element equals to an existing element in the set
    def mkIn(el: ArenaCell, no: Int): Unit = {
      val eq = rewriter.lazyEq.safeEq(resultCell, el) // pre-cached constraints by lazy equality
      // oracle = no => resultcell = el
      rewriter.solverContext.assertGroundExpr(tla.impl(tla.eql(oracle, tla.int(no)), eq))
    }

    elems.zipWithIndex foreach (mkIn _).tupled

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
  def pickTuple(cellType: CellT, state: SymbState, oracle: TlaEx, tuples: Seq[ArenaCell]): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, tuples.map(_.toString).mkString(", ")))
    val tupleType = cellType.asInstanceOf[TupleT]

    var newState = state

    def pickAtPos(i: Int): ArenaCell = {
      // as we know the field index, we just directly project tuples on this index
      val slice = tuples.map(c => newState.arena.getHas(c)(i))
      newState = pickByOracle(newState, oracle, slice)
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
    val newArena = newFields.foldLeft(newState.arena)((a, c) => a.appendHas(newTuple, c))
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
  def pickRecord(cellType: CellT, state: SymbState, oracle: TlaEx, records: Seq[ArenaCell]): SymbState = {
    // since we require all records to have exactly the same type, the code became much simpler
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(cellType, records.map(_.toString).mkString(", ")))
    val recordType = cellType.asInstanceOf[RecordT]

    def findKeyIndex(key: String): Int =
      recordType.fields.keySet.toList.indexOf(key)

    var newState = state

    def pickAtPos(key: String): ArenaCell = {
      val keyIndex = findKeyIndex(key)
      val slice = records.map(c => newState.arena.getHas(c)(keyIndex))
      newState = pickByOracle(newState, oracle, slice)
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
    newArena = fieldCells.foldLeft(newArena)((a, c) => a.appendHas(newRecord, c))
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
  private def pickRecordDomain(domType: CellT, state: SymbState, oracle: TlaEx, domains: Seq[ArenaCell]): SymbState = {
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
      nextState = nextState.setArena(nextState.arena.appendHas(newDom, keyCells))
      // once we know that all the keys coincide, constrain membership with SMT
      for ((dom, no) <- domains.zipWithIndex) {
        def iffKey(keyCell: ArenaCell) = tla.equiv(tla.in(keyCell, newDom), tla.in(keyCell, dom))

        val keysMatch = tla.and(keyCells map iffKey: _*)
        rewriter.solverContext.assertGroundExpr(tla.impl(tla.eql(oracle, tla.int(no)), keysMatch))
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
  def pickSet(cellType: CellT, state: SymbState, oracle: TlaEx, memberSets: Seq[ArenaCell]): SymbState = {
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
      pickSetNonEmpty(cellType, state, oracle, memberSets)
    }
  }

  private def pickSetNonEmpty(cellType: CellT,
                              state: SymbState,
                              oracle: TlaEx,
                              memberSets: Seq[ArenaCell]): SymbState = {
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
      nextState = pickByOracle(nextState, oracle, toPickFrom)
      val picked = nextState.asCell

      // this property is enforced by the oracle magic: chosen = 1 => z_i = c_i /\ chosen = 2 => z_i = d_i

      // The awesome property of the oracle is that we do not have to compare the sets directly!
      // Instead, we compare the oracle values.
      // in(z_i, R) <=> (chosen = 1 /\ in(c_i, S_1) \/ (chosen = 2 /\ in(d_i, S_2)
      def inWhenChosen(elemAndSet: (ArenaCell, ArenaCell), no: Int): TlaEx = {
        if (elemsOfMemberSets(no).nonEmpty) {
          val oracleEqNo = tla.eql(oracle, tla.int(no))
          tla.and(oracleEqNo, tla.in(elemAndSet._1, elemAndSet._2))
        } else {
          tla.bool(false)
        }
      }

      val whenIn = tla.or(toPickFrom.zip(memberSets).zipWithIndex map (inWhenChosen _).tupled: _*)
      // add the cell to the arena
      nextState = nextState.setArena(nextState.arena.appendHas(resultCell, picked))
      // in(z_i, R) <=> (chosen = 1 /\ in(c_i, S_1) \/ (chosen = 2 /\ in(d_i, S_2)
      solverAssert(tla.equiv(tla.in(picked.toNameEx, resultCell.toNameEx), whenIn))
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
  def pickSequence(cellType: CellT, state: SymbState, oracle: TlaEx, memberSeqs: Seq[ArenaCell]): SymbState = {
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
      pickSequenceNonEmpty(cellType, state, oracle, memberSeqs)
    }
  }

  // Pick from a set of sequence. There is a larger overlap with pickSetNonEmpty
  private def pickSequenceNonEmpty(seqType: CellT,
                              state: SymbState,
                              oracle: TlaEx,
                              memberSeqs: Seq[ArenaCell]): SymbState = {
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
      nextState = pickByOracle(nextState, oracle, toPickFrom)
      val picked = nextState.asCell
      // this property is enforced by the oracle magic: chosen = 1 => z_i = c_i /\ chosen = 2 => z_i = d_i
      // add the cell to the arena
      nextState = nextState.setArena(nextState.arena.appendHas(resultCell, picked))
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
  def pickFun(funType: FunT, state: SymbState, oracle: TlaEx, funs: Seq[ArenaCell]): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK %s FROM [%s] {".format(funType, funs.map(_.toString).mkString(", ")))
    var nextState = state
    // pick the relation
    val relationT = FinSetT(TupleT(Seq(funType.argType, funType.resultType)))
    nextState = pickSet(relationT, nextState, oracle, funs map state.arena.getCdm)
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
    * Picks a function from a set [S -> T].
    * Since we construct [S -> T] symbolically, it is easy to pick a function by imposing the constraints
    * from S and T, so we are not using an oracle here.
    *
    * @param funT   a cell type to assign to the picked cell.
    * @param funSet a function set [S -> T]
    * @param state  a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFunFromFunSet(funT: CellT, funSet: ArenaCell, state: SymbState): SymbState = {
    rewriter.solverContext.log("; PICK %s FROM %s {".format(funT, funSet))
    var arena = state.arena
    val dom = arena.getDom(funSet) // this is a set of potential arguments
    val cdm = arena.getCdm(funSet) // this is a set of potential results
    // TODO: take care of [{} -> T] and [S -> {}]
    val funType = funT.asInstanceOf[FunT] // for now, only FunT is supported
    // create the function cell
    arena = arena.appendCell(funT)
    val funCell = arena.topCell
    // create the relation cell
    arena = arena.appendCell(FinSetT(TupleT(Seq(funType.argType, funType.resultType))))
    val relationCell = arena.topCell
    // not keeping the domain explicitly
//    arena = arena.setDom(funCell, dom)
    arena = arena.setCdm(funCell, relationCell)
    var nextState = state.setArena(arena)

    // for every domain cell, pick a result from the co-domain
    for (arg <- arena.getHas(dom)) {
      nextState = pick(cdm, nextState)
      val pickedResult = nextState.asCell

      arena = nextState.arena.appendCell(TupleT(Seq(funType.argType, funType.resultType)))
      val pair = arena.topCell
      arena = arena.appendHas(pair, Seq(arg, pickedResult))
      arena = arena.appendHas(relationCell, pair)
      nextState = nextState.setArena(arena)
      val iff = tla.equiv(tla.in(arg, dom), tla.in(pair, relationCell))
      rewriter.solverContext.assertGroundExpr(iff)
    }
    // TODO: pick default values when one set is empty

    rewriter.solverContext.log("; } PICK %s FROM %s".format(funT, funSet))
    nextState.setRex(funCell)
  }

  /**
    * Implements SE-PICK-FUN, that is, assume that the picked element is a function.
    * This is, by far, the most complex case, and it easily blows up the set of constraints.
    * This method is not used anymore, it is left for reference purposes.
    *
    * @param funType a cell type to assign to the picked cell.
    * @param funs    a sequence of cells that store functions
    * @param state   a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFunPreWarp(funType: FunT, state: SymbState, oracle: NameEx, funs: Seq[ArenaCell]): SymbState = {
    rewriter.solverContext.log(s"; CHERRY-PICK $funType FROM {")
    // pick the domain
    var newState = pickSet(funType.domType, state, oracle, funs map state.arena.getDom)
    val pickedDom = newState.asCell
    newState = newState.setArena(newState.arena.appendCell(FinSetT(funType.resultType)))
    val pickedCdm: ArenaCell = newState.arena.topCell
    // we are not picking the co-domains, as it will make it harder to match
    val cdms = funs map (f => newState.arena.getCdm(f))
    val cdmCells = cdms.map(cdm => Set(newState.arena.getHas(cdm): _*)).reduce(_.union(_))
    val newArena = cdmCells.foldLeft(newState.arena)((a, c) => a.appendHas(pickedCdm, c))
    newState = newState.setArena(newArena)
    // create a fresh cell to hold the function
    newState = newState.setArena(newState.arena.appendCell(funType))
    val funCell = newState.arena.topCell
    newState = newState.setArena(newState.arena.setDom(funCell, pickedDom).setCdm(funCell, pickedCdm))
    // associate a function constant with the function cell
    rewriter.solverContext.declareCellFun(funCell.name, funType.argType, funType.resultType)

    // the pickSet from function domains guarantees us that the constants from pickedDom
    // are equal to the constants from the respective domains
    def resultEqFun(fun_i: ArenaCell, no: Int): Unit = {
      def funAppEq(c_j: ArenaCell): Unit = {
        // chosen = i -> f_new[c_j] = f_i[c_j]
        val chosen = tla.eql(oracle, tla.int(no))
        val funEq = tla.eql(tla.appFun(funCell.toNameEx, c_j.toNameEx),
          tla.appFun(fun_i.toNameEx, c_j.toNameEx))
        rewriter.solverContext.assertGroundExpr(tla.impl(chosen, funEq))
      }

      // chosen = i -> f_new[c_j] = f_i[c_j] for 1 <= i <= n
      val dom_i = newState.arena.getDom(fun_i)
      newState.arena.getHas(dom_i) foreach funAppEq
    }

    funs.zipWithIndex foreach (resultEqFun _).tupled
    rewriter.solverContext.log(s"; } PICK $funCell:$funType")
    newState.setRex(funCell)
  }
}
