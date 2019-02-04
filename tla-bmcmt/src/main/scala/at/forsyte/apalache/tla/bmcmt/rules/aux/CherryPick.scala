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
  *  <li>to pick from a list of cells instead of a set, and</li>
  *  <li>directly uses a choice oracle to avoid multiple comparisons.</li>
  * </ul>
  *
  * @param rewriter a state rewriter
  *
  * @author Igor Konnov
  */
class CherryPick(rewriter: SymbStateRewriter) {
  private val picker = new PickFromAndFunMerge(rewriter, failWhenEmpty = false)

  /**
    * Determine the type of the set elements an element of this type by introducing an oracle
    * @param set a set
    * @param state a symbolic state
    * @return a new symbolic state whose expression stores a fresh cell that corresponds to the picked element.
    */
  def pick(set: ArenaCell, state: SymbState): SymbState = {
    set.cellType match {
      case PowSetT(t@FinSetT(_)) =>
        // a powerset is never empty, pick an element
        picker.pickFromPowset(t, set, state)

      case FinFunSetT(domt@FinSetT(_), cdm@FinSetT(rest)) =>
        // no emptiness check, since we are dealing with a function set [S -> T]
        picker.pickFunFromFunSet(FunT(domt, rest), set, state)

      case _ =>
        val elems = state.arena.getHas(set)
        if (elems.isEmpty) {
          throw new RuntimeException("The set $set is statically empty. Pick should not be called on that.")
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

        pickBlindly(state.setArena(arena), oracle, elems)
    }
  }

  /**
    * Determine the type of the set elements and pick an element of this type.
    *
    * Warning: this method does not check, whether the picked element actually belongs to the set.
    * You have to do it yourself.
    *
    * @param state a symbolic state
    * @param oracle a variable that stores which element (by index) should be picked, can be unrestricted
    * @param elems a non-empty set of cells
    * @return a new symbolic state whose expression stores a fresh cell that corresponds to the picked element.
    */
  def pickBlindly(state: SymbState, oracle: NameEx, elems: Seq[ArenaCell]): SymbState = {
    assert(elems.nonEmpty) // this is an advanced class -- you should know what you are doing
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

      case t@FunT(FinSetT(_), _) =>
        pickFun(t, state, oracle, elems)

      case _ =>
        throw new RewriterException("Cannot pick an element from a set of type: " + targetType)
    }
  }

  /**
    * Pick a basic value, that is, an integer, Boolean, or constant.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param state    a symbolic state
    * @param oracle a variable that stores which element (by index) should be picked, can be unrestricted
    * @param elems a sequence of elements of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickBasic(cellType: CellT, state: SymbState, oracle: NameEx, elems: Seq[ArenaCell]): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK $cellType {")
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
    * @param oracle a variable that stores which element (by index) should be picked, can be unrestricted
    * @param tuples a sequence of records of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickTuple(cellType: CellT, state: SymbState, oracle: NameEx, tuples: Seq[ArenaCell]): SymbState = {
    rewriter.solverContext.log("; CHERRY-PICK $cellType {")
    val tupleType = cellType.asInstanceOf[TupleT]

    var newState = state
    def pickAtPos(i: Int): ArenaCell = {
      // as we know the field index, we just directly project tuples on this index
      val slice = tuples.map(c => newState.arena.getHas(c)(i))
      newState = pickBlindly(newState, oracle, slice)
      newState.asCell
    }

    // introduce a new tuple
    newState = newState.setArena(state.arena.appendCell(cellType))
    val newTuple = newState.arena.topCell
    // for each index i, pick a value from the projection { t[i] : t \in tuples }
    val newFields = tupleType.args.indices map pickAtPos

    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element t[i], as it will use the same oracle!

    // add the new fields to arena
    val newArena = newFields.foldLeft(newState.arena)((a, c) => a.appendHas(newTuple, c))
    rewriter.solverContext.log(s"; } PICK $newTuple:$cellType")
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
    * @param cellType     a cell type to assign to the picked cell.
    * @param state    a symbolic state
    * @param oracle a variable that stores which element (by index) should be picked, can be unrestricted
    * @param records a sequence of records of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickRecord(cellType: CellT, state: SymbState, oracle: NameEx, records: Seq[ArenaCell]): SymbState = {
    // since we require all records to have exactly the same type, the code became much simpler
    rewriter.solverContext.log(s"; CHERRY-PICK $cellType {")
    val recordType = cellType.asInstanceOf[RecordT]
    def findKeyIndex(key: String): Int =
      recordType.fields.keySet.toList.indexOf(key)

    var newState = state

    def pickAtPos(key: String): ArenaCell = {
      val keyIndex = findKeyIndex(key)
      val slice = records.map(c => newState.arena.getHas(c)(keyIndex))
      newState = pickBlindly(newState, oracle, slice)
      newState.asCell
    }

    // introduce a new record
    newState = newState.setArena(state.arena.appendCell(cellType))
    val newRecord = newState.arena.topCell
    // pick the domain using the oracle. TODO: as records have just a few domains, we should be able to optimize it!
    newState = pickSet(FinSetT(ConstT()), newState, oracle, records map (r => newState.arena.getDom(r)))
    val newDom = newState.asCell
    // pick the fields using the oracle
    val fieldCells = recordType.fields.keySet.toSeq map pickAtPos
    // and connect them to the record
    var newArena = newState.arena.setDom(newRecord, newDom)
    newArena = fieldCells.foldLeft(newArena)((a, c) => a.appendHas(newRecord, c))
    // The awesome property: we do not have to enforce equality of the field values, as this will be enforced by
    // the rule for the respective element r.key, as it will use the same oracle!

    rewriter.solverContext.log(s"; } PICK $newRecord:$cellType")

    newState.setArena(newArena)
      .setTheory(CellTheory())
      .setRex(newRecord.toNameEx)
  }

  /**
    * Implements SE-PICK-SET.
    *
    * Note that some record fields may have bogus values, since not all the records in the set
    * are required to have all the keys assigned. That is an unavoidable loophole in the record types.
    *
    * @param cellType     a cell type to assign to the picked cell.
    * @param state    a symbolic state
    * @param oracle a variable that stores which element (by index) should be picked, can be unrestricted
    * @param memberSets a sequence of sets of cellType
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickSet(cellType: CellT, state: SymbState, oracle: NameEx, memberSets: Seq[ArenaCell]): SymbState = {
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
                              oracle: NameEx,
                              memberSets: Seq[ArenaCell]): SymbState = {
    def solverAssert(e: TlaEx): Unit = rewriter.solverContext.assertGroundExpr(e)
    rewriter.solverContext.log(s"; CHERRY-PICK $cellType {")
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

    val maxLen = elemsOfMemberSets map (_.size) reduce((i, j) => if (i > j) i else j)
    assert(maxLen != 0)
    // compute the maximum length
    def padSeq(s: Seq[ArenaCell]): Seq[ArenaCell] = s match {
      // copy last as many times as needed
      case allButLast :+ last => allButLast ++ Seq.fill(maxLen - allButLast.length)(last)
      // the empty sequence is a special case
      case Nil => Nil
    }

    val paddedOfMemberSets = elemsOfMemberSets map padSeq
    val nonEmptyPadded = paddedOfMemberSets.find(_.nonEmpty).get // existence is guaranteed by minPosLen
    // for each index i, create {c_i, ..., d_i}. FIXME: this is not optimal. Implement pick from a static set.
    def pickOneElement(i: Int): Unit = {
      val toPick = paddedOfMemberSets map {
        case Nil => nonEmptyPadded(i) // just use the ith element of the non-empty sequence
        case s => s(i)
      } // no empty sets here
      nextState = pickBlindly(nextState, oracle, toPick)
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

      val whenIn = tla.or(toPick.zip(memberSets).zipWithIndex map (inWhenChosen _).tupled :_*)
      // in(z_i, R) <=> (chosen = 1 /\ in(c_i, S_1) \/ (chosen = 2 /\ in(d_i, S_2)
      solverAssert(tla.equiv(tla.in(picked.toNameEx, resultCell.toNameEx), whenIn))
      // add the cell to the arena
      nextState = nextState.setArena(nextState.arena.appendHas(resultCell, picked))
    }

    0.until(maxLen) foreach pickOneElement

    rewriter.solverContext.log(s"; } CHERRY-PICK $resultCell:$cellType")
    nextState.setRex(resultCell)
  }

  /**
    * Implements SE-PICK-FUN, that is, assume that the picked element is a function.
    * This is, by far, the most complex case, and it easily blows up the set of constraints.
    *
    * @param funType a cell type to assign to the picked cell.
    * @param funs     a sequence of cells that store functions
    * @param state    a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFun(funType: FunT, state: SymbState, oracle: NameEx, funs: Seq[ArenaCell]): SymbState = {
    rewriter.solverContext.log(s"; CHERRY-PICK $funType FROM {")
    // pick the domain
    var newState = pickSet(funType.domType, state, oracle, funs map state.arena.getDom)
    val pickedDom = newState.asCell
    newState = newState.setArena(newState.arena.appendCell(FinSetT(funType.resultType)))
    val pickedCdm: ArenaCell = newState.arena.topCell
    // we are not picking the co-domains, as it will make it harder to match
    val cdms = funs map (f => newState.arena.getCdm(f))
    val cdmCells = cdms.map(cdm => Set(newState.arena.getHas(cdm) :_*)).reduce(_.union(_))
    val newArena = cdmCells.foldLeft(newState.arena) ((a, c) => a.appendHas(pickedCdm, c))
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
