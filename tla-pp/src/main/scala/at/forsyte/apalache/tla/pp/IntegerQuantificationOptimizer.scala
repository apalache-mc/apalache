package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaIntSet, TlaNatSet}

/**
 * This transformation rewrites expressions of the form `\E x \in S: P`, where S is one of `Int`, `Nat`, `a..b`, into
 * `\E x: Q` (unbounded quantification) and `\A x \in S: P` into `\A x: R`.
 *
 * `Q` has the shape `T /\ P`, and `R` has the shape `T => P`, where `T` depends on `S`:
 *   - If `S` is `Int`, `T` is just `TRUE` (and we can say `Q = R = P`)
 *   - If `S` is `Nat`, `T` is `x >= 0`
 *   - If `S` is `a..b`, `T` is `a <= x <= b`
 *
 * This is the only place we support unbounded quantification, as we can leverage the type annotation of `x` (which
 * should be IntT1()). We can then introduce a special rewriting rule for this quantification form.
 *
 * @author
 *   Jure Kukovec
 */

class IntegerQuantificationOptimizer(tracker: TransformationTracker) extends TlaExTransformation {

  private val intTag = Typed(IntT1())
  private val boolTag = Typed(BoolT1())

  override def apply(expr: TlaEx): TlaEx = {
    transform(expr)
  }

  // This optimization only applies to Int, Nat and a..b sets (of integers)
  private def isAllowedSet(s: TlaEx): Boolean = s match {
    case ValEx(TlaIntSet | TlaNatSet)      => true
    case OperEx(TlaArithOper.dotdot, _, _) => true
    case _                                 => false
  }

  // We pass name as String in the next two methods, because re-creating
  // NameEx(name)(intTag) constructs an expression with a fresh UID, thus preserving
  // the property of UID uniqueness. If we had just copied nameEx: NameEx, all the instances
  // of nameEx would have had the same UID.

  // name >= 0
  private def ge0(name: String): TlaEx =
    OperEx(TlaArithOper.ge, NameEx(name)(intTag), ValEx(TlaInt(0))(intTag))(Typed(BoolT1()))

  // lowerBound <= name <= lowerBound
  private def inRange(name: String, lowerBound: TlaEx, upperBound: TlaEx): TlaEx = {
    val lConstraint = OperEx(TlaArithOper.le, lowerBound, NameEx(name)(intTag))(boolTag)
    val uConstraint = OperEx(TlaArithOper.le, NameEx(name)(intTag), upperBound)(boolTag)
    OperEx(TlaBoolOper.and, lConstraint, uConstraint)(boolTag)
  }

  def transform: TlaExTransformation = tracker.trackEx {
    // Assume typechecking succeeded -> name has type Int
    case OperEx(oper @ (TlaBoolOper.forall | TlaBoolOper.exists), nameEx @ NameEx(name), setEx, pred)
        if isAllowedSet(setEx) =>
      // If we have \A, then T => P, otherwise T /\ P
      val (unboundedOper, outerPred) = oper match {
        case TlaBoolOper.forall => (TlaBoolOper.forallUnbounded, TlaBoolOper.implies)
        case TlaBoolOper.exists => (TlaBoolOper.existsUnbounded, TlaBoolOper.and)
      }

      // T depends on the shape of S
      val newPred = setEx match {
        case ValEx(TlaIntSet) => pred
        case ValEx(TlaNatSet) => OperEx(outerPred, ge0(name), pred)(boolTag)
        case OperEx(TlaArithOper.dotdot, lowerBound, upperBound) =>
          OperEx(outerPred, inRange(name, lowerBound, upperBound), pred)(boolTag)
      }
      // nameEx can be copied, and because this is the only place we do so, it will still have a unique ID
      OperEx(unboundedOper, nameEx, newPred)(boolTag)

    case ex => ex
  }
}
