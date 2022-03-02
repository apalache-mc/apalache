package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaIntSet, TlaNatSet}

import com.google.inject.Singleton

/**
 * This transformation rewrites expressions of the form `(\A | \E) x \in S: P`, where S is one of `Int`, `Nat`, `a..b`,
 * into `(\A | \E) x: Q` (unbounded quantification).
 *
 * This is the only place we support unbounded quantification, as we can leverage the type annotation of `x` (which
 * should be IntT1()). We can then introduce a special rewriting rule for this quantification form.
 *
 * @author
 *   Jure Kukovec
 */

@Singleton
class IntegerQuantificationOptimizer(tracker: TransformationTracker) extends TlaExTransformation {

  private val intTag = Typed(IntT1())
  private val boolTag = Typed(BoolT1())

  override def apply(expr: TlaEx): TlaEx = {
    transform(expr)
  }

  // This optimization only applies to Int, Nat and a..b sets (of integers)
  // TODO: Unused ATM, but will be needed when plugging this transformation into preprocessing
  private def isAllowedSet(s: TlaEx): Boolean = s match {
    case ValEx(TlaIntSet | TlaNatSet)      => true
    case OperEx(TlaArithOper.dotdot, _, _) => true
    case _                                 => false
  }

  // Given a quantifier, returns the unbounded variant of the same quantifier.
  def mkUnbounded(op: TlaOper): TlaOper = op match {
    case TlaBoolOper.forall => TlaBoolOper.forallUnbounded
    case TlaBoolOper.exists => TlaBoolOper.existsUnbounded
    case _                  => op
  }

  // name >= 0
  private def ge0(name: String): TlaEx =
    OperEx(TlaArithOper.ge, NameEx(name)(intTag), ValEx(TlaInt(0))(intTag))(Typed(BoolT1()))

  // a <= name <= b
  private def inRange(name: String, lowerBound: TlaEx, upperBound: TlaEx): TlaEx = {
    val lConstraint = OperEx(TlaArithOper.le, lowerBound, NameEx(name)(intTag))(boolTag)
    val uConstraint = OperEx(TlaArithOper.le, NameEx(name)(intTag), upperBound)(boolTag)
    OperEx(TlaBoolOper.and, lConstraint, uConstraint)(boolTag)
  }

  // (\A | \E) x \in S: P transforms into (\A | \E) x: Q
  // For \E x \in S: P,
  // Q := R /\ P, for some R
  // and for \A x \in S: P,
  // Q := R => P, for some R
  private def andOrImpl(op: TlaOper): TlaBoolOper =
    if (op == TlaBoolOper.exists) TlaBoolOper.and
    else TlaBoolOper.implies

  // Creates an expression (\A | \E) x: op(P2,P),
  // where op is either `/\` or `=>`
  private def modifyPred(
      oper: TlaOper,
      nameEx: TlaEx,
      setMemberPred: TlaEx,
      originalPred: TlaEx): TlaEx = {
    val newPred = OperEx(andOrImpl(oper), setMemberPred, originalPred)(boolTag)
    OperEx(mkUnbounded(oper), nameEx, newPred)(boolTag)
  }

  def transform: TlaExTransformation = tracker.trackEx {
    // Assume typechecking succeeded -> name has type Int
    case OperEx(oper @ (TlaBoolOper.forall | TlaBoolOper.exists), nameEx, ValEx(TlaIntSet), pred) =>
      OperEx(mkUnbounded(oper), nameEx, pred)(boolTag)
    case OperEx(oper @ (TlaBoolOper.forall | TlaBoolOper.exists), nameEx @ NameEx(name), ValEx(TlaNatSet), pred) =>
      modifyPred(oper, nameEx, ge0(name), pred)
    case OperEx(oper @ (TlaBoolOper.forall | TlaBoolOper.exists), nameEx @ NameEx(name),
            OperEx(TlaArithOper.dotdot, lowerBound, upperBound), pred) =>
      modifyPred(oper, nameEx, inRange(name, lowerBound, upperBound), pred)
    case ex => ex
  }
}
