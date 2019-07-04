package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.assignments.SpecWithTransitions
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaOper, TlaSetOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.values.TlaBool
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
  * A simple skolemization analysis that transforms a formula in negated normal form
  * and finds the existential quantifiers that stand freely in a formula, that is,
  * not located under any universal quantifier.
  *
  * @author Igor Konnov
  */
class SimpleSkolemization @Inject()(val frexStore: FreeExistentialsStoreImpl) extends LazyLogging {
  /**
    * Transform the transitions into normal form and label the free existential quantifiers.
    *
    * @param spec a specification with identified transitions
    * @return the modified input
    */
  def transformAndLabel(spec: SpecWithTransitions): SpecWithTransitions = {
    val initTransitions = spec.initTransitions map toNegatedForm
    val nextTransitions = spec.nextTransitions map toNegatedForm
    val notInv =
      if (spec.notInvariant.isDefined) Some(toNegatedForm(spec.notInvariant.get)) else None
    val notInvPrime =
      if (spec.notInvariantPrime.isDefined) Some(toNegatedForm(spec.notInvariantPrime.get)) else None
    val constInitPrime =
      if (spec.constInitPrime.isDefined) Some(toNegatedForm(spec.constInitPrime.get)) else None

    initTransitions foreach markFreeExistentials
    nextTransitions foreach markFreeExistentials
    notInv foreach markFreeExistentials
    notInvPrime foreach markFreeExistentials
    constInitPrime foreach markFreeExistentials
    new SpecWithTransitions(spec.rootModule, initTransitions, nextTransitions, constInitPrime, notInv, notInvPrime)
  }

  private def markFreeExistentials(ex: TlaEx): Unit = ex match {
    case OperEx(TlaBoolOper.exists, name, _, pred) =>
      logger.debug(s"added free existential $name (id=${ex.ID})")
      frexStore.store += ex.ID
      markFreeExistentials(pred)

    case OperEx(TlaBoolOper.and, args@_*) =>
      args foreach markFreeExistentials

    case OperEx(TlaBoolOper.or, args@_*) =>
      args foreach markFreeExistentials

    case OperEx(TlaControlOper.ifThenElse, args@_*) =>
      // we do not have to check that the predicate does not have \forall,
      // as we are only concerned with \exists in the scope of \forall
      args foreach markFreeExistentials

    case _ =>
      () // stop here
  }

  private def toNegatedForm(rootExpr: TlaEx): TlaEx = {
    def nnf(neg: Boolean, ex: TlaEx): TlaEx = ex match {
      case ValEx(TlaBool(b)) =>
        tla.bool(b ^ neg)

      case ValEx(_) =>
        throw new RewriterException("Negation should not propagate to a non-boolean constant: " + ex)

      case NameEx(name) =>
        if (neg) tla.not(ex) else ex

      case OperEx(TlaBoolOper.not, arg) =>
        nnf(!neg, arg)

      case ite@OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        // ~ITE(A, B, C) == ITE(A, ~B, ~C)
        OperEx(TlaControlOper.ifThenElse, predEx, nnf(neg, thenEx), nnf(neg, elseEx))

      case OperEx(TlaBoolOper.and, args@_*) =>
        val oper = if (neg) TlaBoolOper.or else TlaBoolOper.and
        OperEx(oper, args map (nnf(neg, _)): _*)

      case OperEx(TlaBoolOper.or, args@_*) =>
        val oper = if (neg) TlaBoolOper.and else TlaBoolOper.or
        OperEx(oper, args map (nnf(neg, _)): _*)

      case OperEx(TlaBoolOper.implies, left, right) =>
        if (neg) {
          tla.and(nnf(neg = false, left), nnf(neg = true, right))
        } else {
          tla.or(nnf(neg = true, left), nnf(neg = false, right))
        }

      case OperEx(TlaBoolOper.equiv, left, right) =>
        if (neg) {
          // ~(A <=> B) to (~A /\ B) \/ (A /\ ~B)
          tla.or(tla.and(nnf(neg = false, left), nnf(neg = true, right)),
            tla.and(nnf(neg = true, left), nnf(neg = false, right)))
        } else {
          // (A <=> B) to (~A /\ ~B) \/ (A /\ B)
          tla.or(tla.and(nnf(neg = false, left), nnf(neg = false, right)),
            tla.and(nnf(neg = true, left), nnf(neg = true, right)))
        }

      case OperEx(TlaBoolOper.exists, x, set, pred) =>
        if (neg) {
          OperEx(TlaBoolOper.forall, x, set, nnf(neg = true, pred))
        } else {
          OperEx(TlaBoolOper.exists, x, set, nnf(neg = false, pred))
        }

      case OperEx(TlaBoolOper.forall, x, set, pred) =>
        if (neg) {
          OperEx(TlaBoolOper.exists, x, set, nnf(neg = true, pred))
        } else {
          OperEx(TlaBoolOper.forall, x, set, nnf(neg = false, pred))
        }

      case OperEx(TlaArithOper.lt, left, right) =>
        OperEx(if (neg) TlaArithOper.ge else TlaArithOper.lt, left, right)

      case OperEx(TlaArithOper.le, left, right) =>
        OperEx(if (neg) TlaArithOper.gt else TlaArithOper.le, left, right)

      case OperEx(TlaArithOper.gt, left, right) =>
        OperEx(if (neg) TlaArithOper.le else TlaArithOper.gt, left, right)

      case OperEx(TlaArithOper.ge, left, right) =>
        OperEx(if (neg) TlaArithOper.lt else TlaArithOper.ge, left, right)

      case OperEx(TlaOper.eq, left, right) =>
        OperEx(if (neg) TlaOper.ne else TlaOper.eq, left, right)

      case OperEx(TlaOper.ne, left, right) =>
        OperEx(if (neg) TlaOper.eq else TlaOper.ne, left, right)

      case OperEx(TlaSetOper.in, left, right) =>
        OperEx(if (neg) TlaSetOper.notin else TlaSetOper.in, left, right)

      case OperEx(TlaSetOper.notin, left, right) =>
        OperEx(if (neg) TlaSetOper.in else TlaSetOper.notin, left, right)

      case OperEx(TlaSetOper.subseteq, left, right) =>
        OperEx(if (neg) TlaSetOper.supsetProper else TlaSetOper.subseteq, left, right)

      case OperEx(TlaSetOper.subsetProper, left, right) =>
        OperEx(if (neg) TlaSetOper.supseteq else TlaSetOper.subsetProper, left, right)

      case OperEx(TlaSetOper.supsetProper, left, right) =>
        OperEx(if (neg) TlaSetOper.subseteq else TlaSetOper.supsetProper, left, right)

      case OperEx(TlaSetOper.supseteq, left, right) =>
        OperEx(if (neg) TlaSetOper.subsetProper else TlaSetOper.supseteq, left, right)

      case OperEx(TlaOper.label, subex, args@_*) =>
        OperEx(TlaOper.label, nnf(neg, subex) +: args: _*)

      case _ =>
        if (!neg)
          ex
        else OperEx(TlaBoolOper.not, ex)
    }

    nnf(neg = false, rootExpr)
  }
}
