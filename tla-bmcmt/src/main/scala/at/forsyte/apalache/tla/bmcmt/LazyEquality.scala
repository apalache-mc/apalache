package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.caches.EqCache
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * Generate equality constraints between cells and cache them to avoid redundant constraints.
  *
  * @author Igor Konnov
  */
class LazyEquality(rewriter: SymbStateRewriter) extends StackableContext {

  private val eqCache = new EqCache(NameEx(rewriter.solverContext.falseConst),
    NameEx(rewriter.solverContext.trueConst))

  /**
    * This method ensure that a pair of its arguments can be safely compared by the SMT equality,
    * that is, all the necessary constraints have been generated with cacheEqualities.
    *
    * @param left  a left cell
    * @param right a right cell
    * @return tla.eql(left, right), provided that left and right can be compared
    */
  def safeEq(left: ArenaCell, right: ArenaCell): TlaEx = {
    if (!left.cellType.comparableWith(right.cellType)) {
      // Trivially not equal due to incomparable types.
      // As this comparison usually indicates a coding problem, throw an exception here.
      // If you still think that this is okay to compare variables of different types, insert a check before safeEq.
      throw new RewriterException("Trivial inequality, as the types are different (check your code): type(%s) = %s, while type(%s) = %s"
        .format(left.name, left.cellType, right.name, right.cellType))
    } else if (left == right) {
      NameEx(rewriter.solverContext.trueConst) // this is just true
    } else {
      val entry = eqCache.get(left, right)
      if (entry.isDefined) {
        eqCache.toTla(left, right, entry.get)
      } else {
        // let's add a bit of German here to indicate that it is really dangerous
        val msg = "VORSICHT! SMT equality should be used only after calling cacheEqualities, unless you know what you are doing."
        throw new RewriterException(msg)
      }
    }
  }

  /**
    * Check that the equality constraints were cached for left and right.
    * Then, if left and right are of comparable types, use SMT equality,
    * otherwise just return false. The difference between safeEq and cachedEq is that
    * safeEq is stricter: it does not allow to compare cells of different types at all.
    * Use cachedEq when you comparisons might involve cells of different types,
    * and it is clear that these elements cannot be equal.
    *
    * @param left  a left cell
    * @param right a right cell
    * @return depending on the types of the both cells, return either (= left right), or false
    */
  def cachedEq(left: ArenaCell, right: ArenaCell): TlaEx = {
    if (left == right) {
      NameEx(rewriter.solverContext.trueConst) // this is just true
    } else {
      val entry = eqCache.get(left, right)
      if (entry.isDefined) {
        eqCache.toTla(left, right, entry.get)
      } else if (!left.cellType.comparableWith(right.cellType)) {
        NameEx(rewriter.solverContext.falseConst) // just false as the types are different
      } else {
        // let's add a bit of German here to indicate that it is really dangerous
        val msg = "VORSICHT! SMT equality should be used only after calling cacheEqualities, unless you know what you are doing."
        throw new RewriterException(msg)
      }
    }
  }

  /**
    * Produce equality constraints for each pair in the sequence, so that we can later compare all the pairs as cells
    * using SMT equality (=). Since equality semantics may require us to rewrite the arena and introduce
    * new SMT constraints, this method may invoke rewriting rules and modify the symbolic state.
    *
    * That the equality constraints were introduced for each pair is recorded in the local cache. Thus, the constraints
    * are generated only once for each pair of cells.
    *
    * @param state a symbolic state to start with
    * @param pairs pairs of cells, for which the equality constraints should be generated
    * @return a new symbolic state that contains the constraints for every pair in the sequence
    */
  def cacheEqConstraints(state: SymbState, pairs: Traversable[(ArenaCell, ArenaCell)]): SymbState = {
    rewriter.solverContext.log("; [START] Caching equality constraints for a sequence: " + pairs)

    def makeOne(state: SymbState, pair: (ArenaCell, ArenaCell)): SymbState = {
      cacheOneEqConstraint(state, pair._1, pair._2)
    }

    val result = pairs.foldLeft(state)(makeOne)
    rewriter.solverContext.log("; [DONE]  Caching equality constraints")
    result
  }


  /**
    * Given a pair of cells, generate equality constraints and return a new symbolic state
    * (leaving the original expression in the state unmodified).
    *
    * @param state a symbolic state
    * @param left  left cell to compare
    * @param right right cell to compare
    * @return a new symbolic state
    */
  def cacheOneEqConstraint(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    val cacheEntry = eqCache.get(left, right)
    if (left == right) {
      state
    } else if (cacheEntry.isDefined) {
      state // do nothing
    } else if (!left.cellType.comparableWith(right.cellType)) {
      // cells of incomparable types cannot be equal
      eqCache.put(left, right, EqCache.FalseEntry())
      state
    } else {
      // generate constraints
      val newState =
        (left.cellType, right.cellType) match {
          case (UnknownT(), UnknownT()) | (BoolT(), _)
               | (_, BoolT()) | (IntT(), IntT()) | (ConstT(), ConstT()) =>
            eqCache.put(left, right, EqCache.EqEntry())
            state // nothing to do, just use the built-in equality

          case (FinSetT(_), FinSetT(_)) =>
            mkSetEq(state, left, right)

          case (FunT(_, _), FunT(_, _)) =>
            mkFunEq(state, left, right)

          case (RecordT(_), RecordT(_)) =>
            mkRecordEq(state, left, right)

          case (TupleT(_), TupleT(_)) =>
            mkTupleEq(state, left, right)

          case _ =>
            throw new CheckerException("Unexpected equality test")
        }

      // return the new state
      newState
    }
  }

  /**
    * Cache the equality as the SMT equality. When we know that we can use SMT equality by construction, e.g.,
    * see PICK FROM {S_1, ..., S_n}, we can tell the cache just to use the SMT equality. Use this method with care,
    * as it can easily produce unsound results!
    *
    * @param left a left cell
    * @param right a right cell
    */
  def cacheAsSmtEqualityByMagic(left: ArenaCell, right: ArenaCell): Unit = {
    eqCache.put(left, right, EqCache.EqEntry())
  }

  private def mkSetEq(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    if (left.cellType == FinSetT(UnknownT()) && state.arena.getHas(left).isEmpty) {
      // The statically empty set is a very special case, as its element type is unknown.
      // Hence, we cannot use SMT equality, as it does not work with different sorts.
      mkEmptySetEq(state, left, right)
    } else if (right.cellType == FinSetT(UnknownT()) && state.arena.getHas(right).isEmpty) {
      mkEmptySetEq(state, right, left) // same here
    } else {
      // in general, we need 2 * |X| * |Y| comparisons
      val leftToRight: SymbState = subsetEq(state, left, right)
      val rightToLeft: SymbState = subsetEq(leftToRight, right, left)
      if (left.cellType.signature == right.cellType.signature) {
        // These two sets have the same signature and thus belong to the same sort.
        // Hence, we can use SMT equality. This equality is needed by uninterpreted functions.
        val eq = tla.equiv(tla.eql(left, right), tla.and(leftToRight.ex, rightToLeft.ex))
        rewriter.solverContext.assertGroundExpr(eq)
        eqCache.put(left, right, EqCache.EqEntry())
      } else {
        // The signatures differ and thus SMT will flag a sort error.
        // Introduce a predicate that carries equality constraints.
        // This predicate is needed for equality and membership tests,
        // e.g., {{}} \in {{{}}}, which are particularly hard to handle.
        // TODO: if two sets S and T are found to be equal, congruence might be violated: f(S) != f(T)
        val pred = tla.name(rewriter.solverContext.introBoolConst())
        rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.and(leftToRight.ex, rightToLeft.ex)))
        eqCache.put(left, right, EqCache.ExprEntry(pred))
      }

      // recover the original expression and theory
      rewriter.coerce(rightToLeft.setRex(state.ex), state.theory)
    }
  }

  // statically empty sets should be handled with care
  private def mkEmptySetEq(state: SymbState, emptySet: ArenaCell, otherSet: ArenaCell): SymbState = {
    val otherElems = state.arena.getHas(otherSet)
    if (otherElems.isEmpty) {
      // That's simple. Two statically empty sets are equal.
      eqCache.put(emptySet, otherSet, EqCache.TrueEntry())
      state
    } else {
      // The other set might be empty in some models. Add a predicate.
      val pred = tla.name(rewriter.solverContext.introBoolConst())
      val emptyEx = tla.and(otherElems.map(e => tla.not(tla.in(e, otherSet))) :_*)
      rewriter.solverContext.assertGroundExpr(tla.eql(pred, emptyEx))
      // this predicate will be later used as an equality test
      eqCache.put(emptySet, otherSet, EqCache.ExprEntry(pred))
      state
    }
  }

  /**
    * Check, whether one set is a subset of another set (not a proper one).
    * This method changed the underlying theory to BoolTheory.
    *
    * Since this operation is tightly related to set equality, we moved it here.
    *
    * @param state a symbolic state
    * @param left  a left cell that holds a set
    * @param right a right cell that holds a set
    * @return a new symbolic state with a (Boolean) predicate equivalent to `left \subseteq right`.
    */
  def subsetEq(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    val leftElems = state.arena.getHas(left)
    val rightElems = state.arena.getHas(right)
    if (leftElems.isEmpty) {
      // SE-SUBSETEQ1
      state.setRex(tla.bool(true)).setTheory(BoolTheory())
    } else if (rightElems.isEmpty) {
      // SE-SUBSETEQ2
      def notIn(le: ArenaCell) = {
        tla.not(tla.in(le, left))
      }

      val pred = tla.name(rewriter.solverContext.introBoolConst())
      rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.and(leftElems.map(notIn): _*)))
      state.setRex(pred).setTheory(BoolTheory())
    } else {
      // SE-SUBSETEQ3
      val newState = cacheEqConstraints(state, leftElems cross rightElems) // cache all the equalities
      def exists(lelem: ArenaCell) = {
        def inAndEq(relem: ArenaCell) = {
          tla.and(tla.in(relem, right), cachedEq(lelem, relem))
        }

        tla.or(rightElems.map(inAndEq): _*)
      }

      def notInOrExists(lelem: ArenaCell) = {
        // BUG: this produced OOM on the inductive invariant of Paxos
        // BUGFIX: push this query to the solver, in order to avoid constructing enormous assertions
        val pred = tla.name(rewriter.solverContext.introBoolConst())
        val iff = tla.equiv(pred, tla.or(tla.not(tla.in(lelem, left)), exists(lelem)))
        rewriter.solverContext.assertGroundExpr(iff)
        pred
      }

      val pred = tla.name(rewriter.solverContext.introBoolConst())
      rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.and(leftElems.map(notInOrExists): _*)))
      newState.setTheory(BoolTheory()).setRex(pred)
    }
  }


  /**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  override def push(): Unit = {
    eqCache.push()
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    eqCache.pop()
  }

  /**
    * Pop the context as many times as needed to reach a given level.
    *
    * @param n pop n times, if n > 0, otherwise, do nothing
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


// function comparison: SE-FUN-EQ4
  private def mkFunEq(state: SymbState, leftFun: ArenaCell, rightFun: ArenaCell): SymbState = {
    val leftDom = state.arena.getDom(leftFun)
    val rightDom = state.arena.getDom(rightFun)
    // produce constraints for the domain equality
    val afterDomEq = cacheOneEqConstraint(state, leftDom, rightDom)

    // produce constraints for each function result
    def eachDomElem(st: SymbState, elem: ArenaCell): SymbState = {
      // rewrite leftFun[elem] = rightFun[elem] into a cell
      val leftResultEqualsRightResult =
        tla.eql(tla.appFun(leftFun, elem),
          tla.appFun(rightFun, elem))
      val nst = rewriter.rewriteUntilDone(st.setTheory(BoolTheory()).setRex(leftResultEqualsRightResult))
      val newEx =
        st.ex match {
          case OperEx(TlaBoolOper.and, es@_*) =>
            val notInDom = tla.not(tla.in(elem, leftDom))
            tla.and(tla.or(notInDom, nst.ex) +: es: _*)

          case _ =>
            throw new RuntimeException("should never happen")
        }
      nst.setRex(newEx)
    }

    val domElems = state.arena.getHas(leftDom)
    val domainsEqual = tla.eql(leftDom, rightDom)
    val afterResEq = domElems.foldLeft(afterDomEq.setRex(tla.and(domainsEqual)))(eachDomElem)
    rewriter.solverContext.assertGroundExpr(tla.equiv(tla.eql(leftFun, rightFun), afterResEq.ex))
    eqCache.put(leftFun, rightFun, EqCache.EqEntry())

    // restore the original expression and theory
    rewriter.coerce(afterResEq.setRex(state.ex), state.theory)
  }

  private def mkRecordEq(state: SymbState, leftRec: ArenaCell, rightRec: ArenaCell): SymbState = {
    val leftType = leftRec.cellType.asInstanceOf[RecordT]
    val rightType = rightRec.cellType.asInstanceOf[RecordT]
    val leftDom = state.arena.getDom(leftRec)
    val rightDom = state.arena.getDom(rightRec)
    val leftElems = state.arena.getHas(leftRec)
    val rightElems = state.arena.getHas(rightRec)
    // the intersection of the keys, as we can assume that the domains are equal
    val commonKeys = leftType.fields.keySet.intersect(rightType.fields.keySet)
    var newState = state
    def keyEq(key: String): TlaEx = {
      val leftIndex = leftType.fields.keySet.toList.indexOf(key)
      val rightIndex = rightType.fields.keySet.toList.indexOf(key)
      val leftElem = leftElems(leftIndex)
      val rightElem = rightElems(rightIndex)
      newState = cacheOneEqConstraint(newState, leftElem, rightElem)
      val (newArena, keyCell) = rewriter.strValueCache.getOrCreate(newState.arena, key)
      newState = newState.setArena(newArena)
      tla.or(tla.notin(keyCell, leftDom), safeEq(leftElem, rightElem))
    }

    newState = cacheOneEqConstraint(newState, leftDom, rightDom)

    val eqs = commonKeys.toList map keyEq
    val cons =
      if (eqs.isEmpty)
        safeEq(leftDom, rightDom)
      else
        tla.and(safeEq(leftDom, rightDom) +: eqs :_*)

    rewriter.solverContext.assertGroundExpr(tla.equiv(tla.eql(leftRec, rightRec), cons))
    eqCache.put(leftRec, rightRec, EqCache.EqEntry())

    // restore the original expression and theory
    rewriter.coerce(newState.setRex(state.ex), state.theory)
  }

  private def mkTupleEq(state: SymbState, left: ArenaCell, right: ArenaCell): SymbState = {
    val leftType = left.cellType.asInstanceOf[TupleT]
    val rightType = right.cellType.asInstanceOf[TupleT]
    if (!leftType.comparableWith(rightType)) {
      state
    } else {
      var newState = state

      def elemEq(lelem: ArenaCell, relem: ArenaCell): TlaEx = {
        newState = cacheOneEqConstraint(newState, lelem, relem)
        safeEq(lelem, relem)
      }

      val leftElems = state.arena.getHas(left)
      val rightElems = state.arena.getHas(right)

      val tupleEq = tla.and(leftElems.zip(rightElems).map(p => elemEq(p._1, p._2)) :_*)
      rewriter.solverContext.assertGroundExpr(tla.equiv(tla.eql(left, right), tupleEq))
      eqCache.put(left, right, EqCache.EqEntry())

      // restore the original expression and theory
      rewriter.coerce(newState.setRex(state.ex), state.theory)
    }
  }
}
