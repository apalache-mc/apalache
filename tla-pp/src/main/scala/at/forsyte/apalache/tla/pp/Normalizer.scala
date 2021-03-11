package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.{FlatLanguagePred, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import javax.inject.Singleton

/**
 * This transformation turns subexpressions of a TLA+ expression into negated normal form.
 *
 * @author Igor Konnov
 */
@Singleton
class Normalizer(tracker: TransformationTracker) extends TlaExTransformation {

  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  def transform: TlaExTransformation = nnf(neg = false)

  private def nnf(neg: Boolean): TlaExTransformation = tracker.trackEx {
    case ValEx(TlaBool(b)) =>
      tla.bool(b ^ neg)

    case vex @ ValEx(_) =>
      vex // this may be called when processing a non-Boolean expression

    case ex @ NameEx(_) =>
      if (neg) tla.not(ex) else ex

    case OperEx(TlaBoolOper.not, arg) =>
      nnf(!neg)(arg)

    case ite @ OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
      // ~ITE(A, B, C) == ITE(A, ~B, ~C)
      val recNnf = nnf(neg)
      OperEx(TlaControlOper.ifThenElse, predEx, recNnf(thenEx), recNnf(elseEx))

    case OperEx(TlaBoolOper.and, args @ _*) =>
      val oper: TlaBoolOper = if (neg) TlaBoolOper.or else TlaBoolOper.and
      OperEx(oper, args map nnf(neg): _*)

    case OperEx(TlaBoolOper.or, args @ _*) =>
      val oper: TlaBoolOper = if (neg) TlaBoolOper.and else TlaBoolOper.or
      OperEx(oper, args map nnf(neg): _*)

    case OperEx(TlaBoolOper.implies, left, right) =>
      val (nnfNonNegated, nnfNegated) = (nnf(neg = false), nnf(neg = true))
      if (neg) {
        tla.and(nnfNonNegated(left), nnfNegated(right))
      } else {
        tla.or(nnfNegated(left), nnfNonNegated(right))
      }

    case equiv @ OperEx(TlaBoolOper.equiv, left, right) =>
      val nnfNonNegated = nnf(neg = false)
      // we do not negate the arguments but recurse to deal with the negations below the tree
      if (!neg) {
        tla.eql(nnfNonNegated(left), nnfNonNegated(right))
      } else {
        tla.neql(nnfNonNegated(left), nnfNonNegated(right))
      }

    case OperEx(TlaBoolOper.exists, x, set, pred) =>
      if (neg) {
        OperEx(TlaBoolOper.forall, x, set, nnf(neg = true)(pred))
      } else {
        OperEx(TlaBoolOper.exists, x, set, nnf(neg = false)(pred))
      }

    case OperEx(TlaBoolOper.forall, x, set, pred) =>
      if (neg) {
        OperEx(TlaBoolOper.exists, x, set, nnf(neg = true)(pred))
      } else {
        OperEx(TlaBoolOper.forall, x, set, nnf(neg = false)(pred))
      }

    case OperEx(TlaArithOper.lt, left, right) =>
      OperEx(if (neg) TlaArithOper.ge else TlaArithOper.lt, left, right)

    case OperEx(TlaArithOper.le, left, right) =>
      OperEx(if (neg) TlaArithOper.gt else TlaArithOper.le, left, right)

    case OperEx(TlaArithOper.gt, left, right) =>
      OperEx(if (neg) TlaArithOper.le else TlaArithOper.gt, left, right)

    case OperEx(TlaArithOper.ge, left, right) =>
      OperEx(if (neg) TlaArithOper.lt else TlaArithOper.ge, left, right)

    case eq @ OperEx(TlaOper.eq, left, right) =>
      if (neg) {
        tla.not(tla.eql(transform(left), transform(right)))
      } else {
        tla.eql(transform(left), transform(right))
      }

    case neq @ OperEx(TlaOper.ne, left, right) =>
      if (neg) {
        tla.eql(transform(left), transform(right))
      } else {
        tla.not(tla.eql(transform(left), transform(right)))
      }

    case OperEx(TlaSetOper.in, left, right) =>
      // use only \in, as \notin is not in KerA+
      if (neg) {
        tla.not(OperEx(TlaSetOper.in, transform(left), transform(right)))
      } else {
        OperEx(TlaSetOper.in, transform(left), transform(right))
      }

    case OperEx(TlaSetOper.notin, left, right) =>
      if (neg) {
        OperEx(TlaSetOper.in, transform(left), transform(right))
      } else {
        tla.not(OperEx(TlaSetOper.in, transform(left), transform(right)))
      }

    case OperEx(TlaSetOper.subseteq, left, right) =>
      OperEx(if (neg) TlaSetOper.supsetProper else TlaSetOper.subseteq, transform(left), transform(right))

    case OperEx(TlaSetOper.subsetProper, left, right) =>
      OperEx(if (neg) TlaSetOper.supseteq else TlaSetOper.subsetProper, transform(left), transform(right))

    case OperEx(TlaSetOper.supsetProper, left, right) =>
      OperEx(if (neg) TlaSetOper.subseteq else TlaSetOper.supsetProper, transform(left), transform(right))

    case OperEx(TlaSetOper.supseteq, left, right) =>
      OperEx(if (neg) TlaSetOper.subsetProper else TlaSetOper.supseteq, transform(left), transform(right))

    case OperEx(TlaOper.label, subex, args @ _*) =>
      OperEx(TlaOper.label, nnf(neg)(subex) +: args: _*)

    case ex @ OperEx(TlaTempOper.diamond, args @ _*) =>
      if (!neg) {
        ex
      } else {
        OperEx(TlaTempOper.box, args map nnf(true): _*)
      }

    case ex @ OperEx(TlaTempOper.box, args @ _*) =>
      if (!neg) {
        ex
      } else {
        OperEx(TlaTempOper.box, args map nnf(true): _*)
      }

    case ex @ OperEx(TlaTempOper.leadsTo, _*) =>
      if (!neg) {
        ex
      } else {
        tla.not(ex) // keep ~(... ~> ...)
      }

    case ex @ OperEx(TlaTempOper.guarantees, _*) =>
      if (!neg) {
        ex
      } else {
        tla.not(ex) // keep ~(... -+-> ...)
      }

    case ex @ OperEx(TlaTempOper.weakFairness, _*) =>
      if (!neg) {
        ex
      } else {
        tla.not(ex) // keep ~WF_vars(A) as ~WF_vars(A)
      }

    case ex @ OperEx(TlaTempOper.strongFairness, _*) =>
      if (!neg) {
        ex
      } else {
        tla.not(ex) // keep ~SF_vars(A) as ~SF_vars(A)
      }

    case LetInEx(body, defs @ _*) =>
      if (neg) {
        // a negation of the let body
        nnfLetIn(neg, body, defs)
      } else {
        // no negation, simply normalize the body and the bodies of the definitions
        def transformDef(decl: TlaOperDecl): TlaOperDecl = decl.copy(body = transform(decl.body))

        LetInEx(transform(body), defs map transformDef: _*)
      }

    case OperEx(oper, args @ _*) =>
      // a non-Boolean operator: transform its arguments, which may be Boolean
      if (neg) {
        tla.not(OperEx(oper, args map transform: _*))
      } else {
        OperEx(oper, args map transform: _*)
      }

    case expr =>
      if (!neg) {
        expr
      } else {
        OperEx(TlaBoolOper.not, expr)
      }
  }

  private def nnfLetIn(neg: Boolean, body: TlaEx, defs: Seq[TlaOperDecl]): TlaEx = {

    /**
     * To handle the case of LET X == ... IN ... ~X ...
     * we introduce a new let-in operator NegX$, the body of which is the
     * nnf transformation of the body of X. Then, we replace all calls to ~X in the
     * LET-IN body with calls to NegX$.
     */
    def negName(n: String): String = s"Neg$n$$"

    val newBody = nnf(neg)(body)

    // We can't just implement ~X for all operators ( e.g. what if X == 1..10 ), just for
    // those that actually appear under negation in the body (and thus must be of type Bool)
    def negAppearingOpers(tlaEx: TlaEx): Set[String] = tlaEx match {
      case OperEx(TlaBoolOper.not, OperEx(TlaOper.apply, NameEx(name))) =>
        Set(name)
      case OperEx(op, args @ _*) =>
        args.map(negAppearingOpers).foldLeft(Set.empty[String]) {
          _ ++ _
        }
      case LetInEx(b, ds @ _*) =>
        ds.map(d => negAppearingOpers(d.body)).foldLeft(negAppearingOpers(b)) {
          _ ++ _
        }
      case _ => Set.empty[String]
    }

    val negOpers = negAppearingOpers(newBody)

    val replacements = negOpers map { opName =>
      ReplaceFixed(tracker)(
          OperEx(TlaBoolOper.not, OperEx(TlaOper.apply, NameEx(opName))),
          OperEx(TlaOper.apply, NameEx(negName(opName)))
      )
    }

    val negReplacedBody = replacements.foldLeft(newBody) { case (b, tr) =>
      tr(b)
    }

    val negDefs = defs withFilter { d => negOpers.contains(d.name) } map { d =>
      d.copy(name = negName(d.name), body = nnf(neg = true)(d.body))
    }

    val newDefs = defs ++ negDefs

    LetInEx(negReplacedBody, newDefs: _*)
  }
}

object Normalizer {
  def apply(tracker: TransformationTracker): Normalizer = {
    new Normalizer(tracker)
  }
}
