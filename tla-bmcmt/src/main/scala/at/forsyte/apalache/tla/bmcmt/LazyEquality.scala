package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.caches.{EqCache, EqCacheSnapshot}
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.rewriter.{ConstSimplifierForSmt, Recoverable}
import at.forsyte.apalache.tla.bmcmt.rules.aux.AuxOps._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{ProtoSeqOps, RecordAndVariantOps}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}
import scalaz.unused

import scala.collection.immutable.SortedMap

/**
 * Generate equality constraints between cells and cache them to avoid redundant constraints.
 *
 * @author
 *   Igor Konnov
 */
class LazyEquality(rewriter: SymbStateRewriter)
    extends StackableContext with Serializable with Recoverable[EqCacheSnapshot] {

  @transient
  private lazy val simplifier = new ConstSimplifierForSmt

  private val eqCache = new EqCache()
  private val protoSeqOps = new ProtoSeqOps(rewriter)
  private val recordOps = new RecordAndVariantOps(rewriter)

  /**
   * This method ensure that a pair of its arguments can be safely compared by the SMT equality, that is, all the
   * necessary constraints have been generated with cacheEqualities.
   *
   * @param left
   *   a left cell
   * @param right
   *   a right cell
   * @return
   *   tla.eql(left, right), provided that left and right can be compared
   */
  def safeEq(left: ArenaCell, right: ArenaCell): BuilderT = {
    if (left == right) {
      tla.bool(true) // this is just true
    } else {
      val entry = eqCache.get(left, right)
      if (entry.isDefined) {
        tla.unchecked(eqCache.toTla(left, right, entry.get))
      } else {
        // let's add a bit of German here to indicate that it is really dangerous
        val msg =
          "VORSICHT! SMT equality should be used only after calling cacheEqualities, unless you know what you are doing."
        throw new RewriterException(msg, NullEx)
      }
    }
  }

  /**
   * Check that the equality constraints were cached for left and right. Then, if left and right are of comparable
   * types, use SMT equality, otherwise just return false. The difference between safeEq and cachedEq is that safeEq is
   * stricter: it does not allow to compare cells of different types at all. Use cachedEq when you comparisons might
   * involve cells of different types, and it is clear that these elements cannot be equal.
   *
   * @param left
   *   a left cell
   * @param right
   *   a right cell
   * @return
   *   depending on the types of the both cells, return either (= left right), or false
   */
  def cachedEq(left: ArenaCell, right: ArenaCell): TlaEx = {
    if (left == right) {
      tla.bool(true) // this is just true
    } else {
      val entry = eqCache.get(left, right)
      if (entry.isDefined) {
        eqCache.toTla(left, right, entry.get)
      } else {
        // let's add a bit of German here to indicate that it is really dangerous
        val msg =
          "VORSICHT! SMT equality should be used only after calling cacheEqualities, unless you know what you are doing."
        throw new RewriterException(msg, NullEx)
      }
    }
  }

  /**
   * Produce equality constraints for each pair in the sequence, so that we can later compare all the pairs as cells
   * using SMT equality (=). Since equality semantics may require us to rewrite the arena and introduce new SMT
   * constraints, this method may invoke rewriting rules and modify the symbolic state.
   *
   * That the equality constraints were introduced for each pair is recorded in the local cache. Thus, the constraints
   * are generated only once for each pair of cells.
   *
   * @param state
   *   a symbolic state to start with
   * @param pairs
   *   pairs of cells, for which the equality constraints should be generated
   * @return
   *   a new symbolic state that contains the constraints for every pair in the sequence
   */
  def cacheEqConstraints(state: SymbState, pairs: Iterable[(ArenaCell, ArenaCell)]): SymbState = {
    rewriter.solverContext.log("; [START] Caching equality constraints for a sequence: " + pairs)

    def makeOne(state: SymbState, pair: (ArenaCell, ArenaCell)): SymbState = {
      cacheOneEqConstraint(state, pair._1, pair._2)
    }

    val result = pairs.foldLeft(state)(makeOne)
    rewriter.solverContext.log("; [DONE]  Caching equality constraints")
    result
  }

  /**
   * Given a pair of cells, generate equality constraints and return a new symbolic state (leaving the original
   * expression in the state unmodified).
   *
   * @param state
   *   a symbolic state
   * @param left
   *   left cell to compare
   * @param right
   *   right cell to compare
   * @return
   *   a new symbolic state
   */
  def cacheOneEqConstraint(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    val cacheEntry = eqCache.get(left, right)
    if (left == right) {
      state
    } else if (cacheEntry.isDefined) {
      state // do nothing
    } else {
      // generate constraints
      val newState =
        (left.cellType, right.cellType) match {
          case (UnknownT(), UnknownT()) | (CellTFrom(BoolT1), _) | (_, CellTFrom(BoolT1)) |
              (CellTFrom(IntT1), CellTFrom(IntT1)) | (CellTFrom(ConstT1(_)), CellTFrom(ConstT1(_))) |
              (CellTFrom(StrT1), CellTFrom(StrT1)) =>
            eqCache.put(left, right, EqCache.EqEntry())
            state // nothing to do, just use the built-in equality

          case (CellTFrom(SetT1(_)), CellTFrom(SetT1(_))) =>
            mkSetEq(state, left, right)

          case (CellTFrom(FunT1(_, _)), CellTFrom(FunT1(_, _))) =>
            mkFunEq(state, left, right)

          case (CellTFrom(RecT1(_)), CellTFrom(RecT1(_))) =>
            mkRecordEq(state, left, right)

          case (CellTFrom(RecRowT1(RowT1(fieldTypes, None))), CellTFrom(RecRowT1(RowT1(fieldTypes2, None)))) =>
            assert(fieldTypes == fieldTypes2, s"Non-matching field types: $fieldTypes != $fieldTypes2")
            mkRowRecordEq(state, fieldTypes, left, right)

          case (CellTFrom(VariantT1(RowT1(options1, None))), CellTFrom(VariantT1(RowT1(options2, None)))) =>
            assert(options1 == options2, s"Non-matching variant options: $options1 != $options2")
            mkVariantEq(state, options1, left, right)

          case (CellTFrom(TupT1(_ @_*)), CellTFrom(TupT1(_ @_*))) =>
            mkTupleEq(state, left, right)

          case (CellTFrom(SeqT1(_)), CellTFrom(SeqT1(_))) =>
            mkSeqEq(state, left, right)

          case (FinFunSetT(_, _), FinFunSetT(_, _)) =>
            mkFunSetEq(state, left, right)

          case (lt, rt) =>
            throw new CheckerException(s"Unexpected equality test over types $lt and $rt", state.ex)
        }

      // return the new state
      newState
    }
  }

  /**
   * Cache the equality as the SMT equality. When we know that we can use SMT equality by construction, e.g., see PICK
   * FROM {S_1, ..., S_n}, we can tell the cache just to use the SMT equality. Use this method with care, as it can
   * easily produce unsound results!
   *
   * @param left
   *   a left cell
   * @param right
   *   a right cell
   */
  def cacheAsSmtEqualityByMagic(left: ArenaCell, right: ArenaCell): Unit = eqCache.put(left, right, EqCache.EqEntry())

  /**
   * Count the number of valid equalities. Use this method only for debugging purposes, as it is quite slow.
   *
   * @return
   *   a pair: the number of valid equalities, and the total number of non-constant equalities
   */
  def countConstantEqualities(): (Int, Int) = {
    val solver = rewriter.solverContext
    def isConstant(pred: TlaEx): Boolean = {
      solver.push()
      solver.assertGroundExpr(pred)
      val exEq = solver.sat()
      solver.pop()
      solver.push()
      solver.assertGroundExpr(tla.not(tla.unchecked(pred)))
      val exNeq = solver.sat()
      solver.pop()
      exEq && !exNeq || exNeq && !exEq
    }

    def onEntry(pair: (ArenaCell, ArenaCell), entryAndLevel: (EqCache.CacheEntry, Int)): Int =
      entryAndLevel._1 match {
        case EqCache.EqEntry() =>
          if (isConstant(tla.eql(pair._1.toBuilder, pair._2.toBuilder))) 1 else 0

        case EqCache.ExprEntry(pred) =>
          if (isConstant(pred)) 1 else 0

        case _ => 0
      }

    def isNonStatic(@unused pair: (ArenaCell, ArenaCell), entryAndLevel: (EqCache.CacheEntry, Int)): Int =
      entryAndLevel._1 match {
        case EqCache.FalseEntry() => 0
        case EqCache.TrueEntry()  => 0
        case _                    => 1
      }

    val eqMap = eqCache.getMap
    val nConst = eqMap.map((onEntry _).tupled).sum
    val nNonStatic = eqMap.map((isNonStatic _).tupled).sum
    (nConst, nNonStatic)
  }

  private def mkSetEq(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    rewriter.solverContext.config.smtEncoding match {
      case SMTEncoding.Arrays =>
        // In the arrays encoding we only cache the equalities between the sets' elements
        val leftElems = state.arena.getHas(left)
        val rightElems = state.arena.getHas(right)
        val nextState = cacheEqConstraints(state, leftElems.cross(rightElems)) // cache all the equalities
        eqCache.put(left, right, EqCache.EqEntry())
        nextState.setRex(state.ex)

      case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
        // in general, we need 2 * |X| * |Y| comparisons
        val leftToRight: SymbState = subsetEq(state, left, right)
        val rightToLeft: SymbState = subsetEq(leftToRight, right, left)
        // the type checker makes sure that this holds true
        assert(left.cellType.signature == right.cellType.signature)
        // These two sets have the same signature and thus belong to the same sort.
        // Hence, we can use SMT equality.
        val eq =
          tla.equiv(tla.eql(left.toBuilder, right.toBuilder),
              tla.and(tla.unchecked(leftToRight.ex), tla.unchecked(rightToLeft.ex)))
        rewriter.solverContext.assertGroundExpr(eq)
        eqCache.put(left, right, EqCache.EqEntry())

        // recover the original expression
        rightToLeft.setRex(state.ex)

      case oddEncodingType =>
        throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
    }
  }

  private def mkFunSetEq(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    val dom1 = state.arena.getDom(left)
    val cdm1 = state.arena.getCdm(left)
    val dom2 = state.arena.getDom(right)
    val cdm2 = state.arena.getCdm(right)
    var nextState = mkSetEq(state, dom1, dom2)
    nextState = mkSetEq(nextState, cdm1, cdm2)
    val eq = tla.equiv(tla.eql(left.toBuilder, right.toBuilder),
        tla.and(tla.eql(dom1.toBuilder, dom2.toBuilder), tla.eql(cdm1.toBuilder, cdm2.toBuilder)))
    rewriter.solverContext.assertGroundExpr(eq)
    eqCache.put(left, right, EqCache.EqEntry())

    // recover the original expression and theory
    nextState.setRex(state.ex)
  }

  /**
   * Check, whether one set is a subset of another set (not a proper one).
   *
   * Since this operation is tightly related to set equality, we moved it here.
   *
   * @param state
   *   a symbolic state
   * @param left
   *   a left cell that holds a set
   * @param right
   *   a right cell that holds a set
   * @return
   *   a new symbolic state with a (Boolean) predicate equivalent to `left \subseteq right`.
   */
  def subsetEq(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    val leftElems = state.arena.getHas(left)
    val rightElems = state.arena.getHas(right)
    if (leftElems.isEmpty) {
      assert(left.cellType != InfSetT(CellTFrom(IntT1)))
      // SE-SUBSETEQ1
      state.setRex(state.arena.cellTrue().toBuilder)
    } else if (rightElems.isEmpty) {
      assert(right.cellType != InfSetT(CellTFrom(IntT1)))
      // SE-SUBSETEQ2
      def notIn(le: ArenaCell) = {
        tla.not(tla.selectInSet(le.toBuilder, left.toBuilder))
      }

      val newState = state.updateArena(_.appendCell(BoolT1))
      val pred = newState.arena.topCell
      rewriter.solverContext.assertGroundExpr(tla.eql(pred.toBuilder, tla.and(leftElems.map(notIn): _*)))
      newState.setRex(pred.toBuilder)
    } else {
      // SE-SUBSETEQ3
      var newState = cacheEqConstraints(state, leftElems.cross(rightElems)) // cache all the equalities
      def exists(lelem: ArenaCell) = {

        // inAndEq checks if lelem is in right
        val inAndEqList = rightElems.map(inAndEq(rewriter, _, lelem, right, lazyEq = true))
        // There are plenty of valid subformulas. Simplify!
        simplifier.applySimplifyShallowToBuilderEx(tla.or(inAndEqList: _*))
      }

      def notInOrExists(lelem: ArenaCell) = {
        val notInOrExists =
          simplifier.applySimplifyShallowToBuilderEx(
              tla.or(tla.not(tla.selectInSet(lelem.toBuilder, left.toBuilder)), exists(lelem))
          )

        if (simplifier.isBoolConst(notInOrExists)) {
          notInOrExists // just return the constant
        } else {
          // BUG: this produced OOM on the inductive invariant of Paxos
          // BUGFIX: push this query to the solver, in order to avoid constructing enormous assertions
          newState = newState.updateArena(_.appendCell(BoolT1))
          val pred = newState.arena.topCell
          rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.equiv(pred.toBuilder, notInOrExists)))
          pred.toBuilder
        }
      }

      val forEachNotInOrExists =
        simplifier.applySimplifyShallowToBuilderEx(tla.and(leftElems.map(notInOrExists): _*))
      newState = newState.updateArena(_.appendCell(BoolT1))
      val pred = newState.arena.topCell
      rewriter.solverContext.assertGroundExpr(tla.eql(pred.toBuilder, forEachNotInOrExists))
      newState.setRex(pred.toBuilder)
    }
  }

  /**
   * Take a snapshot and return it
   *
   * @return
   *   the snapshot
   */
  override def snapshot(): EqCacheSnapshot = {
    eqCache.snapshot()
  }

  /**
   * Recover a previously saved snapshot (not necessarily saved by this object).
   *
   * @param shot
   *   a snapshot
   */
  override def recover(shot: EqCacheSnapshot): Unit = {
    eqCache.recover(shot)
  }

  /**
   * Get the current context level, that is the difference between the number of pushes and pops made so far.
   *
   * @return
   *   the current level, always non-negative.
   */
  override def contextLevel: Int = {
    eqCache.contextLevel
  }

  /**
   * Save the current context and push it on the stack for a later recovery with pop.
   */
  override def push(): Unit = {
    eqCache.push()
  }

  /**
   * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient to
   * save only the latest context.
   */
  override def pop(): Unit = {
    eqCache.pop()
  }

  /**
   * Pop the context as many times as needed to reach a given level.
   *
   * @param n
   *   pop n times, if n > 0, otherwise, do nothing
   */
  override def pop(n: Int): Unit = {
    eqCache.pop(n)
  }

  /**
   * Clean the context
   */
  override def dispose(): Unit = {
    eqCache.dispose()
  }

  /**
   * Compare two functions. In the new implementation, we just compare the associated relations as sets.
   *
   * @param state
   * @param leftFun
   * @param rightFun
   * @return
   *   the new symbolic state
   */
  private def mkFunEq(state: SymbState, leftFun: ArenaCell, rightFun: ArenaCell): SymbState = {
    val leftRel = state.arena.getCdm(leftFun)
    val rightRel = state.arena.getCdm(rightFun)

    rewriter.solverContext.config.smtEncoding match {
      case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
        // We cache the equalities between the elements of the functions' ranges, which are pairs of form <arg,res>
        val leftElems = state.arena.getHas(leftRel)
        val rightElems = state.arena.getHas(rightRel)
        var nextState = cacheEqConstraints(state, leftElems.cross(rightElems)) // Cache all the equalities
        eqCache.put(leftFun, rightFun, EqCache.EqEntry())

        // For the rare case in which one function has an empty domain, we need to be extra careful
        // See https://github.com/apalache-mc/apalache/issues/1811
        val leftDom = nextState.arena.getDom(leftFun)
        val rightDom = nextState.arena.getDom(rightFun)
        nextState = cacheOneEqConstraint(nextState, leftDom, rightDom)
        val funEq = tla.unchecked(cachedEq(leftFun, rightFun))
        rewriter.solverContext.assertGroundExpr(tla.impl(funEq, tla.eql(leftDom.toBuilder, rightDom.toBuilder)))
        // That's it!
        nextState.setRex(state.ex)

      case SMTEncoding.OOPSLA19 =>
        val relEq = mkSetEq(state, leftRel, rightRel)
        rewriter.solverContext.assertGroundExpr(tla.equiv(tla.eql(leftFun.toBuilder, rightFun.toBuilder),
                tla.eql(leftRel.toBuilder, rightRel.toBuilder)))
        eqCache.put(leftFun, rightFun, EqCache.EqEntry())

        // Restore the original expression and theory
        relEq.setRex(state.ex)

      case oddEncodingType =>
        throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
    }
  }

  private def mkRecordEq(state: SymbState, leftRec: ArenaCell, rightRec: ArenaCell): SymbState = {
    def extractRecType: CellT => RecT1 = {
      case CellTFrom(t @ RecT1(_)) => t
      case ct                      => throw new IllegalStateException("Expected a record type, found: " + ct)
    }

    val leftType = extractRecType(leftRec.cellType)
    val rightType = extractRecType(rightRec.cellType)
    val leftDom = state.arena.getDom(leftRec)
    val rightDom = state.arena.getDom(rightRec)
    val leftElems = state.arena.getHas(leftRec)
    val rightElems = state.arena.getHas(rightRec)
    // the intersection of the keys, as we can assume that the static domains are equal
    val commonKeys = leftType.fieldTypes.keySet.intersect(rightType.fieldTypes.keySet)
    var newState = state

    def keyEq(key: String): BuilderT = {
      val leftIndex = leftType.fieldTypes.keySet.toList.indexOf(key)
      val rightIndex = rightType.fieldTypes.keySet.toList.indexOf(key)

      // Our typing rules on records allow records with a subset of the fields in a type
      // which means the function from fields in a record type to elements in an instance
      // of that type are partial.
      val leftElemOpt: Option[ArenaCell] = leftElems.lift(leftIndex)
      val rightElemOpt: Option[ArenaCell] = rightElems.lift(rightIndex)

      (leftElemOpt, rightElemOpt) match {
        // Neither record has the key indicated by its type
        case (None, None)                      => tla.bool(true)
        case (Some(leftElem), Some(rightElem)) => {
          newState = cacheOneEqConstraint(newState, leftElem, rightElem)
          val (newArena, keyCell) =
            rewriter.modelValueCache.getOrCreate(newState.arena, (StrT1.toString, key))
          newState = newState.setArena(newArena)
          // it is safe to use in directly since:
          // (1) the record types coincide,
          // (2) record constructors use RecordDomainCache,
          // (3) and CherryPick uses pickRecordDomain
          val membershipTest = tla.selectInSet(keyCell.toBuilder, leftDom.toBuilder)
          tla.or(tla.not(membershipTest), safeEq(leftElem, rightElem))
        }
        case (Some(_), None) | (None, Some(_)) => tla.bool(false)
      }
    }

    newState = cacheOneEqConstraint(newState, leftDom, rightDom)

    val eqs = commonKeys.toList.map(keyEq)
    val cons =
      if (eqs.isEmpty)
        safeEq(leftDom, rightDom)
      else
        tla.and(safeEq(leftDom, rightDom) +: eqs: _*)

    rewriter.solverContext.assertGroundExpr(tla.equiv(tla.eql(leftRec.toBuilder, rightRec.toBuilder), cons))
    eqCache.put(leftRec, rightRec, EqCache.EqEntry())

    // restore the original expression and theory
    newState.setRex(state.ex)
  }

  private def mkRowRecordEq(
      state: SymbState,
      fieldTypes: SortedMap[String, TlaType1],
      leftRec: ArenaCell,
      rightRec: ArenaCell): SymbState = {
    var nextState = state
    def fieldsEq(name: String): BuilderT = {
      val leftField = recordOps.getField(nextState.arena, leftRec, name)
      val rightField = recordOps.getField(nextState.arena, rightRec, name)
      // The field values may be non-basic expressions. Use lazy equality over them too.
      nextState = cacheOneEqConstraint(nextState, leftField, rightField)
      safeEq(leftField, rightField)
    }

    val allFieldsEq = tla.and(fieldTypes.keys.map { n => fieldsEq(n) }.toSeq: _*)
    rewriter.solverContext.assertGroundExpr(tla.eql(tla.eql(leftRec.toBuilder, rightRec.toBuilder), allFieldsEq))
    eqCache.put(leftRec, rightRec, EqCache.EqEntry())
    nextState
  }

  private def mkVariantEq(
      state: SymbState,
      options: SortedMap[String, TlaType1],
      leftVar: ArenaCell,
      rightVar: ArenaCell): SymbState = {
    var nextState = state
    val leftTag = recordOps.getVariantTag(nextState.arena, leftVar)
    val rightTag = recordOps.getVariantTag(nextState.arena, rightVar)

    def valuesEq(tagName: String): BuilderT = {
      val leftValue = recordOps.getUnsafeVariantValue(nextState.arena, leftVar, tagName)
      val rightValue = recordOps.getUnsafeVariantValue(nextState.arena, rightVar, tagName)
      // The field values may be non-basic expressions. Use lazy equality over them too.
      nextState = cacheOneEqConstraint(nextState, leftValue, rightValue)
      // Get the tag as a cell
      nextState = recordOps.getOrCreateVariantTag(nextState, tagName)
      val tagAsCell = nextState.asCell
      // tag = leftTag => leftValue = rightValue
      tla
        .or(tla.not(tla.eql(tagAsCell.toBuilder, leftTag.toBuilder)), safeEq(leftValue, rightValue))
    }

    val tagsEq = tla.eql(leftTag.toBuilder, rightTag.toBuilder)
    val tagsAndValuesEq =
      tla.and(tagsEq +: options.keys.toSeq.map { n => valuesEq(n) }: _*)
    rewriter.solverContext.assertGroundExpr(tla.eql(tla.eql(leftVar.toBuilder, rightVar.toBuilder), tagsAndValuesEq))
    eqCache.put(leftVar, rightVar, EqCache.EqEntry())
    nextState
  }

  private def mkTupleEq(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    var newState = state

    def elemEq(lelem: ArenaCell, relem: ArenaCell): BuilderT = {
      newState = cacheOneEqConstraint(newState, lelem, relem)
      safeEq(lelem, relem)
    }

    val leftElems = state.arena.getHas(left)
    val rightElems = state.arena.getHas(right)

    val tupleEq = tla.and(leftElems.zip(rightElems).map(p => elemEq(p._1, p._2)): _*)
    rewriter.solverContext.assertGroundExpr(tla.equiv(tla.eql(left.toBuilder, right.toBuilder), tupleEq))
    eqCache.put(left, right, EqCache.EqEntry())

    // restore the original expression and theory
    newState.setRex(state.ex)
  }

  private def mkSeqEq(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    val (proto1, len1, capacity1) = protoSeqOps.unpackSeq(state.arena, left)
    val (proto2, len2, capacity2) = protoSeqOps.unpackSeq(state.arena, right)

    // The proto sequences may have different capacities.
    // Since we compare lengths, we only have to compare the shared prefix.
    val sharedCapacity = Math.min(capacity1, capacity2)
    val elems1 = protoSeqOps.elems(state.arena, proto1).slice(0, sharedCapacity)
    val elems2 = protoSeqOps.elems(state.arena, proto2).slice(0, sharedCapacity)

    // compare the shared prefix
    require(len1.cellType == CellTFrom(IntT1))
    require(len2.cellType == CellTFrom(IntT1))
    var nextState = state
    val len1Ex = len1.toBuilder
    val len2Ex = len2.toBuilder

    def eqPairwise(indexBase1: Int, cells: (ArenaCell, ArenaCell)): BuilderT = {
      nextState = cacheOneEqConstraint(nextState, cells._1, cells._2)
      // Either (1) one of the lengths is below the index, or (2) the elements are equal.
      // The case (1) is compensated with the constraint sizesEq below.
      val outside1 = tla.lt(len1Ex, tla.int(indexBase1))
      val outside2 = tla.lt(len2Ex, tla.int(indexBase1))
      tla.or(outside1, outside2, safeEq(cells._1, cells._2))
    }

    val elemsEq = tla.and(1.to(sharedCapacity).zip(elems1.zip(elems2)).map((eqPairwise _).tupled): _*)
    val sizesEq = tla.eql(len1Ex, len2Ex)

    // seq1 and seq2 are equal if and only if: (1) their lengths are equal, and (2) their shared prefixes are equal.
    rewriter.solverContext
      .assertGroundExpr(tla.equiv(tla.eql(left.toBuilder, right.toBuilder), tla.and(sizesEq, elemsEq)))
    eqCache.put(left, right, EqCache.EqEntry())

    // restore the original expression and theory
    nextState.setRex(state.ex)
  }
}
