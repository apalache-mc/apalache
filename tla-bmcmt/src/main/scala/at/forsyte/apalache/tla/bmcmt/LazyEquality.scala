package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

import scala.collection.mutable

/**
  * Generate equality constraints between cells and cache them to avoid redundant constraints.
  *
  * @author Igor Konnov
  */
class LazyEquality(solverContext: SolverContext) {
  // store in cache, whether a pair of cells has been compared before
  private var eqCache: mutable.HashSet[(ArenaCell, ArenaCell)] = new mutable.HashSet[(ArenaCell, ArenaCell)]()

  /**
    * Given a pair of cells, generate equality constraints and return a TLA+ expression over cells
    * that can be used in SolverContext.assertGroundExpr.
    *
    * @param arena an arena
    * @param left  left cell to compare
    * @param right right cell to compare
    * @return a TLA+ cell expression
    */
  def mkEquality(arena: Arena, left: ArenaCell, right: ArenaCell): TlaEx = {
    if (!left.cellType.comparableWith(right.cellType)) {
      // cells of incomparable types cannot be equal
      ValEx(TlaFalse)
    } else {
      if (eqCache.contains((left, right)) || eqCache.contains((right, left))) {
        // the constraints are already in the cache, we can just write down an SMT equality
        OperEx(TlaOper.eq, left.toNameEx, right.toNameEx)
      } else {
        // generate constraints
        (left.cellType, right.cellType) match {
          case (UnknownT(), UnknownT())
               | (BoolT(), _) | (_, BoolT()) =>
            () // do nothing, just use the built-in equality

          case (IntT(), IntT()) =>
            // compare using two integer constants that will
            // be compared with valInt(left) and valInt(right)
            // TODO: find a more optimal solution?
            val leftInt = solverContext.introIntConst()
            val rightInt = solverContext.introIntConst()
            // left = right iff leftInt = rightInt
            val cellEqIffIntEq = OperEx(TlaBoolOper.equiv,
              OperEx(TlaOper.eq, left.toNameEx, right.toNameEx),
              OperEx(TlaOper.eq, NameEx(leftInt), NameEx(rightInt)))
            // leftInt = valInt(left) and rightInt = valInt(right)
            val leftIntEqLeftCell = OperEx(TlaOper.eq, NameEx(leftInt), left.toNameEx)
            val rightIntEqRightCell = OperEx(TlaOper.eq, NameEx(rightInt), right.toNameEx)
            solverContext.assertGroundExpr(leftIntEqLeftCell)
            solverContext.assertGroundExpr(rightIntEqRightCell)
            solverContext.assertGroundExpr(cellEqIffIntEq)

          case (FinSetT(_), FinSetT(_)) =>
            // in general, we need 2 * |X| * |Y| comparisons
            val leftSubsetEqRight = subsetEq(arena, left, right)
            val rightSubsetEqLeft = subsetEq(arena, right, left)
            val eq = OperEx(TlaBoolOper.equiv,
              OperEx(TlaOper.eq, left.toNameEx, right.toNameEx),
              OperEx(TlaBoolOper.and, leftSubsetEqRight, rightSubsetEqLeft))
            solverContext.assertGroundExpr(eq)

          case (FunT(_, _), FunT(_, _)) =>
            throw new CheckerException("Comparison of functions is not implemented yet")

          case _ =>
            throw new CheckerException("Unexpected equality test")
        }
        // cache that we have built the constraints
        eqCache.add((left, right))
        // return a comparison
        OperEx(TlaOper.eq, left.toNameEx, right.toNameEx)
      }
    }
  }

  private def subsetEq(arena: Arena, left: ArenaCell, right: ArenaCell) = {
    val leftElems = arena.getHas(left)
    val rightElems = arena.getHas(right)
    if (leftElems.isEmpty) {
      // SE-SUBSETEQ1
      ValEx(TlaTrue)
    } else if (rightElems.isEmpty) {
      // SE-SUBSETEQ2
      def notIn(le: ArenaCell) = {
        OperEx(TlaBoolOper.not, OperEx(TlaSetOper.in, le.toNameEx, left.toNameEx))
      }

      OperEx(TlaBoolOper.and, leftElems.map(notIn): _*)
    } else {
      // SE-SUBSETEQ3
      def exists(lelem: ArenaCell) = {
        def inAndEq(relem: ArenaCell) = {
          OperEx(TlaBoolOper.and,
            OperEx(TlaSetOper.in, relem.toNameEx, right.toNameEx),
            mkEquality(arena, lelem, relem))
        }

        val rightIn = rightElems.map(inAndEq)
        OperEx(TlaBoolOper.or, rightIn: _*)
      }

      def notInOrExists(lelem: ArenaCell) = {
        OperEx(TlaBoolOper.or,
          OperEx(TlaBoolOper.not,
            OperEx(TlaSetOper.in, lelem.toNameEx, left.toNameEx)),
          exists(lelem))
      }

      OperEx(TlaBoolOper.and, leftElems.map(notInOrExists): _*)
    }
  }
}
