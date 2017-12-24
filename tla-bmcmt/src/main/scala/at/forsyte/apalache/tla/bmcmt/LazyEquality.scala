package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

import scala.collection.mutable

/**
  * Generate equality constraints between cells and cache them to avoid redundant constraints.
  *
  * @author Igor Konnov
  */
class LazyEquality(rewriter: SymbStateRewriter) extends StackableContext {
  /**
    * The current context level, see StackableContext.
    */
  private var level: Int = 0

  /**
    * A set of pairs, for which the equality constraints have been generated in SMT.
    * This set can be partially cleaned up, when the pop method is called.
    */
  private var eqCache: mutable.Set[(ArenaCell, ArenaCell)] = new mutable.HashSet[(ArenaCell, ArenaCell)]()

  /**
    * For each level i, maintain the list of entries that were introduced level i, so we can easily remove
    * the entries for the level i by iterating over the list in levelEntries[i].
    * Here, we use a list, the head stores the entries that have been introduced at the current level.
    */
  private var entriesPerLevel: List[List[(ArenaCell, ArenaCell)]] = List(List())

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
    } else if (eqCache.contains((left, right))) {
      tla.eql(left, right) // it is safe to use SMT equality, as we have constructed the constraints
    } else if (eqCache.contains((right, left))) {
      tla.eql(right, left) // it is safe to use SMT equality, as we have constructed the constraints
    } else {
      // let's add a bit of German here to indicate that it is really dangerous
      val msg = "VORSICHT! SMT equality should be used only after calling cacheEqualities, unless you know what you are doing."
      throw new RewriterException(msg)
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
    if (!left.cellType.comparableWith(right.cellType)) {
      // cells of incomparable types cannot be equal
      if (!eqCache.contains((left, right)) && !eqCache.contains((right, left))) {
        rewriter.solverContext.assertGroundExpr(tla.neql(left, right))
      }
      state
    } else {
      if (left == right) {
        // there is nothing to do
        state
      } else if (eqCache.contains((left, right)) || eqCache.contains((right, left))) {
        // the constraints are already in the cache, we can just write down an SMT equality
        OperEx(TlaOper.eq, left.toNameEx, right.toNameEx)
        eqCache.add((left, right)) // remember that we have generated the equality constraints
        entriesPerLevel = ((left, right) +: entriesPerLevel.head) +: entriesPerLevel.tail // add entry on the head
        state
      } else {
        // generate constraints
        val newState =
          (left.cellType, right.cellType) match {
            case (UnknownT(), UnknownT()) | (BoolT(), _) | (_, BoolT()) =>
              state // nothing to do, just use the built-in equality

            case (IntT(), IntT()) =>
              // compare using two integer constants that will
              // be compared with valInt(left) and valInt(right)
              // TODO: find a more optimal solution?
              val leftInt = rewriter.solverContext.introIntConst()
              val rightInt = rewriter.solverContext.introIntConst()
              // left = right iff leftInt = rightInt
              val cellEqIffIntEq = OperEx(TlaBoolOper.equiv,
                OperEx(TlaOper.eq, left.toNameEx, right.toNameEx),
                OperEx(TlaOper.eq, NameEx(leftInt), NameEx(rightInt)))
              // leftInt = valInt(left) and rightInt = valInt(right)
              val leftIntEqLeftCell = OperEx(TlaOper.eq, NameEx(leftInt), left.toNameEx)
              val rightIntEqRightCell = OperEx(TlaOper.eq, NameEx(rightInt), right.toNameEx)
              rewriter.solverContext.assertGroundExpr(leftIntEqLeftCell)
              rewriter.solverContext.assertGroundExpr(rightIntEqRightCell)
              rewriter.solverContext.assertGroundExpr(cellEqIffIntEq)
              state

            case (FinSetT(_), FinSetT(_)) =>
              // in general, we need 2 * |X| * |Y| comparisons
              val leftToRight: SymbState = subsetEq(state, left, right)
              val rightToLeft: SymbState = subsetEq(leftToRight, right, left)
              val eq = tla.equiv(tla.eql(left, right), tla.and(leftToRight.ex, rightToLeft.ex))
              rewriter.solverContext.assertGroundExpr(eq)
              // recover the original expression and theory
              rewriter.coerce(rightToLeft.setRex(state.ex), state.theory)

            case (FunT(_, _), FunT(_, _)) =>
              mkFunEq(state, left, right)

            case _ =>
              throw new CheckerException("Unexpected equality test")
          }

        eqCache.add((left, right)) // remember that we have generated the equality constraints
        entriesPerLevel = ((left, right) +: entriesPerLevel.head) +: entriesPerLevel.tail // add entry on the head
        // return the new state
        newState
      }
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
          tla.and(tla.in(relem, right), tla.eql(lelem, relem))
        }

        tla.or(rightElems.map(inAndEq): _*)
      }

      def notInOrExists(lelem: ArenaCell) = {
        tla.or(tla.not(tla.in(lelem, left)), exists(lelem))
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
    level += 1
    entriesPerLevel = List() +: entriesPerLevel // one more level
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    assert(level > 0)
    for (entry <- entriesPerLevel.head) {
      eqCache.remove(entry)
    }
    entriesPerLevel = entriesPerLevel.tail
    level -= 1
  }

  /**
    * Pop the context as many times as needed to reach a given level.
    *
    * @param n the number of times to call pop
    */
  override def pop(n: Int): Unit = {
    for (_ <- 1.to(n)) {
      pop()
    }
  }

  /**
    * Clean the context.
    */
  override def dispose(): Unit = {
    eqCache.clear()
    entriesPerLevel = List(List())
    level = 0
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
    // restore the original expression and theory
    rewriter.coerce(afterResEq.setRex(state.ex), state.theory)
  }

}
