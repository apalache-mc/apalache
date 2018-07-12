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
  * Currently, we allow a pick to fail and return an arbitrary value (of given sort).
  * By default, failWhenEmpty = false, as the mode failWhenEmpty = true produces too many false positives...
  *
  * @param rewriter      a state rewriter
  * @param failWhenEmpty issue a failure predicate that is set to true when a given set is empty
  *
  * @author Igor Konnov
  */
class PickFromAndFunMerge(rewriter: SymbStateRewriter, failWhenEmpty: Boolean = false) {
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

      case PowSetT(t @ FinSetT(_)) =>
        // a powerset is never empty, pick an element
        pickFromPowset(t, set, state)

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
    rewriter.solverContext.log("; PICK %s FROM %s {".format(cellType, set))
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
    rewriter.solverContext.log("; } PICK %s FROM %s".format(cellType, set))
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
    rewriter.solverContext.log("; PICK %s FROM %s {".format(cellType, set))
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
    rewriter.solverContext.log("; } PICK %s FROM %s".format(cellType, set))
    state.setArena(arena).setRex(resultCell)
  }

  /**
    * Implements SE-PICK-SET, that is, assume that the picked element is a set itself.
    *
    * @param resultType a cell type to assign to the picked cell.
    * @param set      a powerset
    * @param state    a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickFromPowset(resultType: CellT, set: ArenaCell, state: SymbState): SymbState = {
    // TODO: add this rule to the report!
    rewriter.solverContext.log("; PICK %s FROM %s {".format(resultType, set))
    var arena = state.arena.appendCell(resultType)
    val resultSet = arena.topCell
    val baseSet = arena.getDom(set)
    val elems = arena.getHas(baseSet)
    // resultSet may contain all the elements from the baseSet of the powerset SUBSET(S)
    arena = elems.foldLeft(arena)((a, e) => a.appendHas(resultSet, e))

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
    * Implements SE-PICK-TUPLE.
    *
    * @param cellType a cell type to assign to the picked cell.
    * @param tupleSet a set of cells that store tuples
    * @param state    a symbolic state
    * @return a new symbolic state with the expression holding a fresh cell that stores the picked element.
    */
  def pickTuple(cellType: CellT, tupleSet: ArenaCell, state: SymbState): SymbState = {
    rewriter.solverContext.log("; PICK %s FROM %s {".format(cellType, tupleSet))
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
    rewriter.solverContext.log("; } PICK %s FROM %s".format(cellType, tupleSet))
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
    // TODO: refactor, this happened to be a lot of code
    rewriter.solverContext.log("; PICK %s FROM %s {".format(cellType, recordSet))
    val recordType = cellType.asInstanceOf[RecordT]
    val records = state.arena.getHas(recordSet)

    def pickAtPos(key: String, sAndL: (SymbState, List[ArenaCell])): (SymbState, List[ArenaCell]) = {
      def hasKey(rec: ArenaCell): Boolean =
        rec.cellType.asInstanceOf[RecordT].fields.contains(key)

      def keyIndex(rec: ArenaCell): Int =
        rec.cellType.asInstanceOf[RecordT].fields.keySet.toList.indexOf(key)

      val filteredRecs = records filter hasKey // not all the records have to have the key
      val tuples = filteredRecs.map(c => sAndL._1.arena.getHas(c).head) // the underlying tuples
      // get all the values that match the key and eliminate the duplicates
      val indices = filteredRecs map keyIndex
      val values = Set[ArenaCell](tuples.zip(indices) map { case (t, i) => sAndL._1.arena.getHas(t)(i) }: _*)
      if (values.isEmpty) {
        // this is just wrong: we could not have computed such a record type by unification
        throw new RewriterException(s"Internal error, no values for the record key $key in the set $recordSet")
      }

      // Pick a value. The set may be dynamically empty. We add necessary constraints below.
      val valueSet = tla.enumSet(values.toList.map(_.toNameEx): _*)
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
    // compute the constants for each key, as we have to connect them with the domain
    def mapKey(key: String): (String, ArenaCell) = {
      val (newArena, cell) = rewriter.strValueCache.getOrCreate(arena, key)
      arena = arena
      (key, cell)
    }

    val keyMap = Map[String, ArenaCell](recordType.fields.keySet.toList.map(mapKey): _*)
    // introduce the record domain
    arena = arena.appendCell(FinSetT(ConstT()))
    val newDomain = arena.topCell
    arena = arena.setDom(newRecord, newDomain)
    arena = keyMap.values.foldLeft(arena)((a, c) => a.appendHas(newDomain, c))

    // introduce a new failure predicate
    arena = arena.appendCell(FailPredT())
    val failPred = arena.topCell
    // pick the values for each key
    val (newState: SymbState, newCells: List[ArenaCell]) =
      recordType.fields.keySet.foldRight((state.setArena(arena), List[ArenaCell]()))(pickAtPos)
    // and connect them to the underlying tuple
    arena = newCells.foldLeft(newState.arena)((a, c) => a.appendHas(newTuple, c))

    def forceEquality(otherRecord: ArenaCell): TlaEx = {
      def otherDomain = arena.getDom(otherRecord)

      def valueEq(key: String): TlaEx = {
        val otherType = otherRecord.cellType.asInstanceOf[RecordT]
        if (!otherType.fields.contains(key)) {
          tla.notin(keyMap(key), newDomain)
        } else {
          // the values record[key] and otherRecord[key] must be equal
          val index = recordType.fields.keySet.toList.indexOf(key)
          val elem = newCells(index)
          val otherIndex = otherType.fields.keySet.toList.indexOf(key)
          val otherTuple = arena.getHas(otherRecord).head
          val otherElem = arena.getHas(otherTuple)(otherIndex)
          // check the domain
          val inOtherDom = tla.in(keyMap(key).toNameEx, otherDomain)
          val inDom = tla.in(keyMap(key).toNameEx, newDomain)
          val eq = rewriter.lazyEq.safeEq(elem, otherElem)
          tla.or(tla.and(tla.not(inOtherDom), tla.not(inDom)),
            tla.and(eq, inDom, inOtherDom))
        }
      }

      val valueEqualities = recordType.fields.keySet.toList map valueEq
      tla.and(tla.in(otherRecord, recordSet) +: valueEqualities: _*)
    }

    val existsFun = tla.or(records map forceEquality: _*)
    val existsFunOrFailure = decorateWithFailure(existsFun, recordSet, records, newRecord, failPred)
    rewriter.solverContext.assertGroundExpr(existsFunOrFailure)
    rewriter.solverContext.log("; } PICK %s FROM %s".format(cellType, recordSet))

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
    rewriter.solverContext.log("; PICK %s FROM %s {".format(cellType, funSet))
    val newState = funMerge(state, funSet) // introduce DOM and CDM, see SE-PICK-FUN
    var arena = newState.arena
    val dom = arena.getDom(funSet)
    val cdm = arena.getCdm(funSet)
    val funType = cellType.asInstanceOf[FunT] // for now, it should be FunT, neither tuple nor record
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
    rewriter.solverContext.log("; } PICK %s FROM %s".format(cellType, funSet))
    newState.setArena(arena).setRex(funCell)
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
    rewriter.solverContext.log("; PICK %s FROM %s {".format(cellType, funSet))
    var arena = state.arena
    val dom = arena.getDom(funSet)
    val cdm = arena.getCdm(funSet)
    val funType = cellType.asInstanceOf[FunT] // for now, only FinT is supported
    arena = arena.appendCell(cellType)
    val funCell = arena.topCell

    //    BUG: add a function to a set, pick it from a set, apply this function => failure as the domain may be empty

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
    rewriter.solverContext.log("; } PICK %s FROM %s".format(cellType, funSet))
    state.setArena(arena).setRex(funCell)
  }

  /**
    * Implements the rule SE-FUN-MERGE: it extracts the domains and co-domains from all the cells stored in the set
    * and decorates the set cell with the edges 'dom' and 'cdm' that point to the unions of all domains and co-domains,
    * respectively.
    *
    * @param state      a symbolic state
    * @param funSetCell a set of cells that store functions
    * @return the new state, in which funSetCell has two links:
    *         dom for the union of element domains and cdm for the union of element domains
    */
  def funMerge(state: SymbState, funSetCell: ArenaCell): SymbState = {
    rewriter.solverContext.log("; FUN-MERGE %s {".format(funSetCell))
    var arena = state.arena
    if (arena.hasDom(funSetCell) && arena.hasCdm(funSetCell)) {
      rewriter.solverContext.log("; } FUN-MERGE %s".format(funSetCell))
      state
    } else {
      val (argType: CellT, resultType: CellT) = funSetCell.cellType match {
        case FinSetT(FunT(FinSetT(at), rt)) =>
          (at, rt)

        case _ =>
          throw new RewriterException("Unexpected type for a set of functions: " + funSetCell.cellType)
      }

      val allDoms = Set(arena.getHas(funSetCell).map(c => arena.getDom(c)): _*).toList
      val allCdms = Set(arena.getHas(funSetCell).map(e => arena.getCdm(e)): _*).toList
      val unionOfAllDoms = tla.union(tla.enumSet(allDoms.map(_.toNameEx): _*))
      val domState = rewriter.rewriteUntilDone(state.setRex(unionOfAllDoms))
      val unionOfAllCdms = tla.union(tla.enumSet(allCdms.map(_.toNameEx): _*))
      val cdmState = rewriter.rewriteUntilDone(domState.setRex(unionOfAllCdms))
      arena = cdmState.arena

      arena = arena.setDom(funSetCell, domState.arena.findCellByNameEx(domState.ex))
      arena = arena.setCdm(funSetCell, cdmState.arena.findCellByNameEx(cdmState.ex))

      rewriter.solverContext.log("; } FUN-MERGE %s".format(funSetCell))
      cdmState.setArena(arena).setRex(state.ex).setTheory(state.theory)
    }
  }

  // wrap an SMT constraint with a failure case
  private def decorateWithFailure(found: TlaEx, set: ArenaCell, setElems: Seq[ArenaCell],
                                  result: ArenaCell, failure: ArenaCell): TlaEx = {
    def mkNotIn(domElem: ArenaCell): TlaEx = {
      tla.not(tla.in(domElem, set))
    }
    val setEmptyInRuntime =
      if (setElems.isEmpty) tla.bool(true) else tla.and(setElems.map(mkNotIn): _*)

    if (!failWhenEmpty) {
      // Do nothing, e.g., when \E x \in S is translated to S /= {} /\ x = PICK ... FROM S,
      // the pick operator should not issue any errors, as the set emptiness is resolved by other means.
      tla.or(tla.and(tla.or(found, setEmptyInRuntime), tla.not(failure)))
    } else {
      rewriter.solverContext.log("; decorate with failure, set: %s, result: %s".format(set, result))

      if (setElems.isEmpty) {
        failure // statically flag a failure
      } else {
        // 1. The condition 'found' should hold true, when there is no failure.
        // 2. If there is a failure, no guarantess are given.
        // 3. A failure happens if and only if the set is empty at runtime.
        tla.or(tla.and(tla.not(failure), found),
          tla.and(failure, setEmptyInRuntime))
      }
    }
  }
}
