package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * Rewriting for the syntactic form PICK _: tau FROM ... and FUN-MERGE.
  * Importantly, the user picks the type tau somewhat arbitrary, and a new cell is assigned type tau.
  * So, it is up to the user to ensure that the cells in the set have types compatible with tau.
  *
  * TODO: check for empty sets, statically and dynamically
  *
  * @author Igor Konnov
  */
class PickFromAndFunMerge(rewriter: SymbStateRewriter) {
  /**
    * Determine the general type of the set elements and pick an element of this type.
    *
    * @param set   a set cell
    * @param state a symbolic state
    * @return a new symbolic state whose expression stores a fresh cell that corresponds to the picked element.
    */
  def pick(set: ArenaCell, state: SymbState): SymbState = {
    def checkEmptiness(): Unit =
      if (state.arena.getHas(set).isEmpty)
      // there is nothing to pick from a statically empty set
        throw new RewriterException("Picking an element from a statically empty set")

    set.cellType match {
      case FinSetT(ConstT()) =>
        checkEmptiness()
        pickBasic(ConstT(), set, state)

      case FinSetT(IntT()) =>
        checkEmptiness()
        pickBasic(IntT(), set, state)

      case FinSetT(BoolT()) =>
        checkEmptiness()
        pickBasic(BoolT(), set, state)

      case FinSetT(t@FinSetT(_)) =>
        checkEmptiness()
        pickSet(t, set, state)

      case FinSetT(t@FunT(FinSetT(argt), rest)) =>
        checkEmptiness()
        pickFun(t, set, state)

      case FinSetT(t@TupleT(_)) =>
        checkEmptiness()
        pickTuple(t, set, state)

      case FinSetT(t@RecordT(_)) =>
        checkEmptiness()
        pickRecord(t, set, state)

      case FinFunSetT(domt@FinSetT(_), cdm@FinSetT(rest)) =>
        // no emptiness check, since we are dealing with a function set [S -> T]
        pickFunFromFunSet(FunT(domt, rest), set, state)

      case _ =>
        throw new RewriterException("Cannot pick an element from a set of type: " + set.cellType)
    }
  }

  /**
    * Implements SE-PICK-BASIC, that is, assume that the picked element has one of the basic types:
    * integer, Boolean, or constant.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param set      a set of cells
    * @param state    a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickBasic(cellType: CellT, set: ArenaCell, state: SymbState): SymbState = {
    var arena = state.arena.appendCell(cellType)
    val resultCell = arena.topCell
    // introduce a new failure predicate
    arena = arena.appendCell(FailPredT())
    val failPred = arena.topCell
    // compare the set contents with the result
    val setCells = arena.getHas(set)
    val eqState = rewriter.lazyEq.cacheEqConstraints(state, setCells.map(e => (e, resultCell)))

    // the new element equals to an existing element in the set
    def mkIn(domElem: ArenaCell): TlaEx = {
      val inSet = tla.in(domElem, set)
      tla.and(inSet, rewriter.lazyEq.safeEq(domElem, resultCell)) // pre-cached constraints by lazy equality
    }

    val found = tla.or(setCells.map(mkIn): _*)
    val existsBasicOrFailure = decorateWithFailure(found, set, setCells, resultCell, failPred)
    rewriter.solverContext.assertGroundExpr(existsBasicOrFailure)
    eqState.setArena(arena).setRex(resultCell)
  }

  /**
    * Implements SE-PICK-SET, that is, assume that the picked element is a set itself.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param set      a set of cells
    * @param state    a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickSet(cellType: CellT, set: ArenaCell, state: SymbState): SymbState = {
    var arena = state.arena.appendCell(cellType)
    val resultCell = arena.topCell
    arena = arena.appendCell(cellType)
    val auxCell = arena.topCell
    // introduce a new failure predicate
    arena = arena.appendCell(FailPredT())
    val failPred = arena.topCell

    val elems = arena.getHas(set)
    // get all the cells pointed by the elements of the set
    val union = elems.map(e => Set(arena.getHas(e): _*))
      .fold(Set[ArenaCell]())(_ union _)

    // the resulting cell points to all the cells in the union
    arena = union.foldLeft(arena)((a, e) => a.appendHas(resultCell, e))

    // the auxillary cell equals to an element in the original set
    def mkIn(setElem: ArenaCell): TlaEx = {
      val inSet = tla.in(setElem, set)
      // here we don't use the deep equality, just the SMT equality
      val eq = tla.eql(setElem, auxCell)
      tla.and(inSet, eq)
    }

    def mkNotIn(setElem: ArenaCell): TlaEx = {
      tla.not(tla.in(setElem, set))
    }

    def inResultIffInAux(elem: ArenaCell): Unit = {
      val inResult = tla.in(elem, resultCell)
      val inAux = tla.in(elem, auxCell)
      rewriter.solverContext.assertGroundExpr(tla.equiv(inResult, inAux))
    }

    union.foreach(inResultIffInAux)
    val found = tla.or(elems.map(mkIn): _*)
    val existsSetOrFailure = decorateWithFailure(found, set, elems, resultCell, failPred)
    rewriter.solverContext.assertGroundExpr(existsSetOrFailure)
    state.setArena(arena).setRex(resultCell)
  }

  /**
    * Implements SE-PICK-TUPLE.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param tupleSet a set of cells that store tuples
    * @param state    a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickTuple(cellType: CellT, tupleSet: ArenaCell, state: SymbState): SymbState = {
    val tupleType = cellType.asInstanceOf[TupleT]
    val tuples = state.arena.getHas(tupleSet)

    def pickAtPos(i: Int, sAndL: (SymbState, List[ArenaCell])): (SymbState, List[ArenaCell]) = {
      val slice = tuples.map(c => sAndL._1.arena.getHas(c)(i))
      val sliceSet = tla.enumSet(slice.map(_.toNameEx): _*)
      val newState = rewriter.rewriteUntilDone(sAndL._1.setRex(sliceSet).setTheory(CellTheory()))
      val sliceSetCell = newState.arena.findCellByNameEx(newState.ex)
      val pickedState = pick(sliceSetCell, newState)
      val pickedCell = pickedState.arena.findCellByNameEx(pickedState.ex)
      val eqState = rewriter.lazyEq.cacheEqConstraints(pickedState, slice.map(c => (c, pickedCell)))
      (eqState, pickedCell +: sAndL._2)
    }

    // introduce a new tuple
    var arena = state.arena.appendCell(cellType)
    val newTuple = arena.topCell
    // introduce a new failure predicate
    arena = arena.appendCell(FailPredT())
    val failPred = arena.topCell
    val (newState: SymbState, newCells: List[ArenaCell]) =
      tupleType.args.indices.foldRight((state.setArena(arena), List[ArenaCell]()))(pickAtPos)

    def forceEquality(otherTuple: ArenaCell): TlaEx = {
      def eq(p: (ArenaCell, ArenaCell)): TlaEx = {
        rewriter.lazyEq.safeEq(p._1, p._2)
      }

      val equalities = newCells.zip(arena.getHas(otherTuple)) map eq
      tla.and(tla.in(otherTuple, tupleSet) +: equalities: _*)
    }

    val existsFun = tla.or(tuples map forceEquality: _*)
    val existsFunOrFailure = decorateWithFailure(existsFun, tupleSet, tuples, newTuple, failPred)
    rewriter.solverContext.assertGroundExpr(existsFunOrFailure)

    arena = newCells.foldLeft(newState.arena)((a, c) => a.appendHas(newTuple, c))
    newState.setArena(arena)
      .setTheory(CellTheory())
      .setRex(newTuple.toNameEx)
  }

  /**
    * Implements SE-PICK-RECORD.
    *
    * Note that some record fields may have bogus values, since not all the records in the set
    * are required to have all the keys assigned. That is an unavoidable loophole in the record types.
    *
    * @param cellType  a cell type to assign to the picked cell.
    * @param recordSet a set of cells that store records
    * @param state     a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickRecord(cellType: CellT, recordSet: ArenaCell, state: SymbState): SymbState = {
    val recordType = cellType.asInstanceOf[RecordT]
    val records = state.arena.getHas(recordSet)

    def pickAtPos(key: String, sAndL: (SymbState, List[ArenaCell])): (SymbState, List[ArenaCell]) = {
      def hasKey(rec: ArenaCell): Boolean =
        rec.cellType.asInstanceOf[RecordT].fields.contains(key)

      def keyIndex(rec: ArenaCell): Int =
        rec.cellType.asInstanceOf[RecordT].fields.keySet.toList.indexOf(key)

      val filteredRecs = records filter hasKey // not all the records have to have the key
      val tuples = filteredRecs.map(c => sAndL._1.arena.getHas(c).head) // the underlying tuples
      // get all the values that match the key
      val indices = filteredRecs map keyIndex
      val values = tuples.zip(indices) map { case (t, i) => sAndL._1.arena.getHas(t)(i) }
      if (values.isEmpty) {
        // this is just wrong: we could not have computed such a record type by unification
        throw new RewriterException(s"Internal error, no values for the record key $key in the set $recordSet")
      }

      // Pick a value. The set may be dynamically empty. We add necessary constraints below.
      val valueSet = tla.enumSet(values.map(_.toNameEx): _*)
      val newState = rewriter.rewriteUntilDone(sAndL._1.setRex(valueSet).setTheory(CellTheory()))
      val valueSetCell = newState.arena.findCellByNameEx(newState.ex)
      val pickedState = pick(valueSetCell, newState)
      val pickedCell = pickedState.arena.findCellByNameEx(pickedState.ex)
      // don't forget to add equality constraints, as we have to compare the values below
      val eqState = rewriter.lazyEq.cacheEqConstraints(pickedState, values.map(c => (c, pickedCell)))
      (eqState, pickedCell +: sAndL._2)
    }

    // introduce a new record and the underlying tuple
    var arena = state.arena.appendCell(cellType)
    val newRecord = arena.topCell
    val tupleType = TupleT(recordType.fields.values.toList) // NB: fields are sorted by keys
    arena = arena.appendCell(tupleType)
    val newTuple = arena.topCell
    arena = arena.appendHas(newRecord, newTuple) // bind the record to the tuple
    // introduce a new failure predicate
    arena = arena.appendCell(FailPredT())
    val failPred = arena.topCell
    // pick the values for each key
    val (newState: SymbState, newCells: List[ArenaCell]) =
      recordType.fields.keySet.foldRight((state.setArena(arena), List[ArenaCell]()))(pickAtPos)
    // and connect them to the underlying tuple
    arena = newCells.foldLeft(newState.arena)((a, c) => a.appendHas(newTuple, c))

    def forceEquality(otherRecord: ArenaCell): TlaEx = {
      def valueEq(key: String): TlaEx = {
        val otherType = otherRecord.cellType.asInstanceOf[RecordT]
        if (!otherType.fields.contains(key)) {
          tla.bool(true) // no key, no constraint
        } else {
          // the values record[key] and otherRecord[key] must be equal
          val index = recordType.fields.keySet.toList.indexOf(key)
          val elem = newCells(index)
          val otherIndex = otherType.fields.keySet.toList.indexOf(key)
          val otherTuple = arena.getHas(otherRecord).head
          val otherElem = arena.getHas(otherTuple)(otherIndex)
          rewriter.lazyEq.safeEq(elem, otherElem)
        }
      }

      val valueEqualities = recordType.fields.keySet.toList map valueEq
      tla.and(tla.in(otherRecord, recordSet) +: valueEqualities: _*)
    }

    val existsFun = tla.or(records map forceEquality: _*)
    val existsFunOrFailure = decorateWithFailure(existsFun, recordSet, records, newRecord, failPred)
    rewriter.solverContext.assertGroundExpr(existsFunOrFailure)

    newState.setArena(arena)
      .setTheory(CellTheory())
      .setRex(newRecord.toNameEx)
  }

  /**
    * Implements SE-PICK-FUN, that is, assume that the picked element is a function.
    * This is, by far, the most complex case, and it easily blows up the set of constraints.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param funSet   a set of cells that store functions
    * @param state    a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFun(cellType: CellT, funSet: ArenaCell, state: SymbState): SymbState = {
    var arena = funMerge(state.arena, funSet) // introduce DOM and CDM, see SE-PICK-FUN
    val dom = arena.getDom(funSet)
    val cdm = arena.getCdm(funSet)
    val funType = cellType.asInstanceOf[FunT] // for now, it should be FunT, no tuple or record
    arena = arena.appendCell(cellType)
    val funCell = arena.topCell
    arena = arena.setDom(funCell, dom).setCdm(funCell, cdm)
    // introduce a new failure predicate
    arena = arena.appendCell(FailPredT())
    val failPred = arena.topCell
    // associate a function constant with the function cell
    rewriter.solverContext.declareCellFun(funCell.name, funType.argType, funType.resultType)

    // push the constraints to SMT
    val domElems = arena.getHas(dom)

    def resultEqFun(fun_i: ArenaCell): TlaEx = {
      val dom_i = arena.getDom(fun_i) // dom_i, i.e., the domain of f_{c_i}
      def inDom(c_j: ArenaCell): TlaEx = {
        // c_j \in dom <=> c_j \in DOMAIN(fun_i)
        tla.equiv(tla.in(c_j, dom), tla.in(c_j, dom_i))
      }

      def funAppEq(c_j: ArenaCell): TlaEx = {
        // c_j \in dom => f_new[c_j] = f_{fun_i}[c_j]
        tla.impl(tla.in(c_j, dom),
          tla.eql(tla.appFun(funCell, c_j),
            tla.appFun(fun_i, c_j)))
      }

      // in(c_i, c_set) /\ f_new[c'_j] = f_{c_1}[c'_j] /\ ... /\ f_new[c'_j] = f_{c_i}[c'_j]
      val inDomAndFunAppEq = domElems.map(funAppEq) ++ domElems.map(inDom)
      tla.and(tla.in(fun_i, funSet) +: inDomAndFunAppEq: _*)
    }

    val funSetElems = arena.getHas(funSet)
    val existsFun = tla.or(funSetElems.map(resultEqFun): _*)
    val existsFunOrFailure = decorateWithFailure(existsFun, funSet, funSetElems, funCell, failPred)
    rewriter.solverContext.assertGroundExpr(existsFunOrFailure)
    state.setArena(arena).setRex(funCell)
  }

  /**
    * Implements SE-PICK-SET-FUN, that is, pick a function from a set [S -> T].
    * Since we construct [S -> T] symbolically, it is easy to pick a function by imposing the constraints
    * from S and T.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param funSet   a function set [S -> T]
    * @param state    a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFunFromFunSet(cellType: CellT, funSet: ArenaCell, state: SymbState): SymbState = {
    var arena = state.arena
    val dom = arena.getDom(funSet)
    val cdm = arena.getCdm(funSet)
    val funType = cellType.asInstanceOf[FunT] // for now, only FinT is supported
    arena = arena.appendCell(cellType)
    val funCell = arena.topCell
    arena = arena.setDom(funCell, dom).setCdm(funCell, cdm)
    // introduce a new failure predicate
    arena = arena.appendCell(FailPredT())
    val failPred = arena.topCell
    // associate a function constant with the function cell
    val resultType = cellType match {
      case FunT(_, rt) => rt
      case _ => throw new RewriterException(s"Unexpected cell type $cellType in pickFun")
    }
    rewriter.solverContext.declareCellFun(funCell.name, funType.argType, funType.resultType)
    // push the constraints to SMT
    val cdmElems = arena.getHas(cdm)

    def resultInCdm(domElem: ArenaCell): TlaEx = {
      def funAppInCdm(cdmElem: ArenaCell): TlaEx = {
        // cdmElem \in cdm /\ f_new[domElem] = cdmElem
        tla.and(tla.in(cdmElem, cdm),
          tla.eql(tla.appFun(funCell, domElem), cdmElem))
      }

      tla.or(tla.not(tla.in(domElem, dom)) +: cdmElems.map(funAppInCdm): _*)
    }

    val domElems = arena.getHas(dom)
    val existsFun = tla.and(domElems.map(resultInCdm): _*)
    val existsFunOrFailure = decorateWithFailure(existsFun, funSet, domElems, funCell, failPred)
    rewriter.solverContext.assertGroundExpr(existsFunOrFailure)
    state.setArena(arena).setRex(funCell)
  }

  /**
    * Implements the rule SE-FUN-MERGE: it extracts the domains and co-domains from all the cells stored in the set
    * and decorates the set cell with the edges 'dom' and 'cdm' that point to the unions of all domains and co-domains,
    * respectively.
    *
    * @param arena      an arena
    * @param funSetCell a set of cells that store functions
    * @return the new arena, in which funSetCell has two links:
    *         dom for the union of element domains and cdm for the union of element domains
    */
  def funMerge(arena: Arena, funSetCell: ArenaCell): Arena = {
    if (arena.hasDom(funSetCell) && arena.hasCdm(funSetCell)) {
      arena
    } else {
      val (argType: CellT, resultType: CellT) = funSetCell.cellType match {
        case FinSetT(FunT(FinSetT(at), rt)) =>
          (at, rt)

        case _ =>
          throw new RewriterException("Unexpected type for a set of functions: " + funSetCell.cellType)
      }

      val (newArena: Arena, cells: Seq[ArenaCell]) = arena.appendCellSeq(FinSetT(argType), FinSetT(resultType))
      val dom = cells.head
      val cdm = cells.tail.head
      val domUnion = arena.getHas(funSetCell).map(e => Set(arena.getHas(arena.getDom(e)): _*))
        .fold(Set[ArenaCell]())(_ union _)
      val cdmUnion = arena.getHas(funSetCell).map(e => Set(arena.getHas(arena.getCdm(e)): _*))
        .fold(Set[ArenaCell]())(_ union _)
      val newArena2 = domUnion.foldLeft(newArena)((a, e) => a.appendHas(dom, e))
      val newArena3 = cdmUnion.foldLeft(newArena2)((a, e) => a.appendHas(cdm, e))
      newArena3.setDom(funSetCell, dom).setCdm(funSetCell, cdm)
    }
  }

  // wrap an SMT constraint with a failure case
  private def decorateWithFailure(found: TlaEx, set: ArenaCell, setElems: Seq[ArenaCell],
                                  result: ArenaCell, failure: ArenaCell): TlaEx = {
    def mkNotIn(domElem: ArenaCell): TlaEx = {
      tla.not(tla.in(domElem, set))
    }

    val setEmptyInRuntime = tla.and(setElems.map(mkNotIn): _*)
    if (setElems.isEmpty) {
      failure // statically flag a failure
    } else {
      tla.and(tla.and(tla.not(failure), found), tla.eql(failure, setEmptyInRuntime))
    }
  }
}
