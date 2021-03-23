package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.{FlatLanguagePred, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.{BoolT1, OperT1}

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
    case ex @ ValEx(TlaBool(b)) =>
      OperEx(TlaBoolOper.not, ValEx(TlaBool(b ^ neg))(ex.typeTag))(ex.typeTag)

    case vex @ ValEx(_) =>
      vex // this may be called when processing a non-Boolean expression

    case ex @ NameEx(_) =>
      if (neg) {
        OperEx(TlaBoolOper.not, ex)(ex.typeTag)
      } else {
        ex
      }

    case OperEx(TlaBoolOper.not, arg) =>
      nnf(!neg)(arg)

    case ite @ OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
      // ~ITE(A, B, C) == ITE(A, ~B, ~C)
      val recNnf = nnf(neg)
      OperEx(TlaControlOper.ifThenElse, predEx, recNnf(thenEx), recNnf(elseEx))(ite.typeTag)

    case ex @ OperEx(TlaBoolOper.and, args @ _*) =>
      val oper: TlaBoolOper = if (neg) TlaBoolOper.or else TlaBoolOper.and
      OperEx(oper, args map nnf(neg): _*)(ex.typeTag)

    case ex @ OperEx(TlaBoolOper.or, args @ _*) =>
      val oper: TlaBoolOper = if (neg) TlaBoolOper.and else TlaBoolOper.or
      OperEx(oper, args map nnf(neg): _*)(ex.typeTag)

    case ex @ OperEx(TlaBoolOper.implies, left, right) =>
      val (nnfNonNegated, nnfNegated) = (nnf(neg = false), nnf(neg = true))
      if (neg) {
        OperEx(TlaBoolOper.and, nnfNonNegated(left), nnfNegated(right))(ex.typeTag)
      } else {
        OperEx(TlaBoolOper.or, nnfNegated(left), nnfNonNegated(right))(ex.typeTag)
      }

    case equiv @ OperEx(TlaBoolOper.equiv, left, right) =>
      val nnfNonNegated = nnf(neg = false)
      // we do not negate the arguments but recurse to deal with the negations below the tree
      if (!neg) {
        OperEx(TlaOper.eq, nnfNonNegated(left), nnfNonNegated(right))(equiv.typeTag)
      } else {
        OperEx(TlaOper.ne, nnfNonNegated(left), nnfNonNegated(right))(equiv.typeTag)
      }

    case ex @ OperEx(TlaBoolOper.exists, x, set, pred) =>
      if (neg) {
        OperEx(TlaBoolOper.forall, x, transform(set), nnf(neg = true)(pred))(ex.typeTag)
      } else {
        OperEx(TlaBoolOper.exists, x, transform(set), nnf(neg = false)(pred))(ex.typeTag)
      }

    case ex @ OperEx(TlaBoolOper.forall, x, set, pred) =>
      if (neg) {
        OperEx(TlaBoolOper.exists, x, transform(set), nnf(neg = true)(pred))(ex.typeTag)
      } else {
        OperEx(TlaBoolOper.forall, x, transform(set), nnf(neg = false)(pred))(ex.typeTag)
      }

    case ex @ OperEx(TlaArithOper.lt, left, right) =>
      if (neg) {
        OperEx(TlaArithOper.ge, left, right)(ex.typeTag)
      } else {
        ex
      }

    case ex @ OperEx(TlaArithOper.le, left, right) =>
      if (neg) {
        OperEx(TlaArithOper.gt, left, right)(ex.typeTag)
      } else {
        ex
      }

    case ex @ OperEx(TlaArithOper.gt, left, right) =>
      if (neg) {
        OperEx(TlaArithOper.le, left, right)(ex.typeTag)
      } else {
        ex
      }

    case ex @ OperEx(TlaArithOper.ge, left, right) =>
      if (neg) {
        OperEx(TlaArithOper.lt, left, right)(ex.typeTag)
      } else {
        ex
      }

    case eq @ OperEx(TlaOper.eq, left, right) =>
      val trEq = OperEx(TlaOper.eq, transform(left), transform(right))(eq.typeTag)
      if (neg) {
        OperEx(TlaBoolOper.not, trEq)(eq.typeTag)
      } else {
        trEq
      }

    case neq @ OperEx(TlaOper.ne, left, right) =>
      val trEq = OperEx(TlaOper.eq, transform(left), transform(right))(neq.typeTag)
      if (neg) {
        trEq
      } else {
        OperEx(TlaBoolOper.not, trEq)(neq.typeTag)
      }

    case in @ OperEx(TlaSetOper.in, left, right) =>
      // use only \in, as \notin is not in KerA+
      val trIn = OperEx(TlaSetOper.in, transform(left), transform(right))(in.typeTag)
      if (neg) {
        OperEx(TlaBoolOper.not, trIn)(in.typeTag)
      } else {
        trIn
      }

    case notin @ OperEx(TlaSetOper.notin, left, right) =>
      val trIn = OperEx(TlaSetOper.in, transform(left), transform(right))(notin.typeTag)
      if (neg) {
        trIn
      } else {
        OperEx(TlaBoolOper.not, trIn)(notin.typeTag)
      }

    case lex @ OperEx(TlaOper.label, subex, args @ _*) =>
      OperEx(TlaOper.label, nnf(neg)(subex) +: args: _*)(lex.typeTag)

    case ex @ OperEx(TlaTempOper.diamond, args @ _*) =>
      if (!neg) {
        OperEx(TlaTempOper.diamond, args map transform: _*)(ex.typeTag)
      } else {
        OperEx(TlaTempOper.box, args map nnf(true): _*)(ex.typeTag)
      }

    case ex @ OperEx(TlaTempOper.box, args @ _*) =>
      if (!neg) {
        OperEx(TlaTempOper.box, args map nnf(true): _*)(ex.typeTag)
      } else {
        OperEx(TlaTempOper.diamond, args map transform: _*)(ex.typeTag)
      }

    case ex @ OperEx(TlaTempOper.leadsTo, args @ _*) =>
      if (!neg) {
        OperEx(TlaTempOper.leadsTo, args map transform: _*)(ex.typeTag)
      } else {
        OperEx(TlaBoolOper.not, ex)(ex.typeTag) // keep ~(... ~> ...)
      }

    case ex @ OperEx(TlaTempOper.guarantees, args @ _*) =>
      if (!neg) {
        OperEx(TlaTempOper.guarantees, args map transform: _*)(ex.typeTag)
      } else {
        OperEx(TlaBoolOper.not, ex)(ex.typeTag) // keep ~(... -+-> ...)
      }

    case ex @ OperEx(TlaTempOper.weakFairness, args @ _*) =>
      if (!neg) {
        OperEx(TlaTempOper.weakFairness, args map transform: _*)(ex.typeTag)
      } else {
        OperEx(TlaBoolOper.not, ex)(ex.typeTag) // keep ~WF_vars(A) as ~WF_vars(A)
      }

    case ex @ OperEx(TlaTempOper.strongFairness, args @ _*) =>
      if (!neg) {
        OperEx(TlaTempOper.strongFairness, args map transform: _*)(ex.typeTag)
      } else {
        OperEx(TlaBoolOper.not, ex)(ex.typeTag) // keep ~SF_vars(A) as ~SF_vars(A)
      }

    case letIn @ LetInEx(body, defs @ _*) =>
      if (neg) {
        // a negation of the let body
        nnfLetIn(neg, body, defs)
      } else {
        // no negation, simply normalize the body and the bodies of the definitions
        def transformDef(decl: TlaOperDecl): TlaOperDecl = decl.copy(body = transform(decl.body))

        LetInEx(transform(body), defs map transformDef: _*)(letIn.typeTag)
      }

    case ex @ OperEx(oper, args @ _*) =>
      // a non-Boolean operator: transform its arguments, which may be Boolean
      if (neg) {
        // why do we add a Boolean negation on top?
        OperEx(TlaBoolOper.not, OperEx(oper, args map transform: _*)(ex.typeTag))(ex.typeTag)
      } else {
        OperEx(oper, args map transform: _*)(ex.typeTag)
      }

    case expr =>
      if (!neg) {
        expr
      } else {
        // why do we add a Boolean negation on top?
        OperEx(TlaBoolOper.not, expr)(expr.typeTag)
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

    val toBoolT = OperT1(Seq(), BoolT1())

    // We can't just implement ~X for all operators ( e.g. what if X == 1..10 ), just for
    // those that actually appear under negation in the body (and thus must be of type Bool)
    def negAppearingOpers(tlaEx: TlaEx): Set[String] = tlaEx match {
      case OperEx(TlaBoolOper.not, OperEx(TlaOper.apply, NameEx(name))) if tlaEx.typeTag == Typed(toBoolT) =>
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
      val toReplace = tla.not(tla.appOp(tla.name(opName) ? "b") ? "b").typed(Map("b" -> BoolT1()), "b")
      lazy val replacement = tla
        .appOp(tla.name(negName(opName)) ? "op")
        .typed(Map("b" -> BoolT1(), "op" -> toBoolT), "b")
      ReplaceFixed(tracker)(toReplace, replacement)
    }

    val negReplacedBody = replacements.foldLeft(newBody) { case (b, tr) =>
      tr(b)
    }

    val negDefs = defs withFilter { d => negOpers.contains(d.name) } map { d =>
      d.copy(name = negName(d.name), body = nnf(neg = true)(d.body))
    }

    val newDefs = defs ++ negDefs

    LetInEx(negReplacedBody, newDefs: _*)(body.typeTag)
  }
}

object Normalizer {
  def apply(tracker: TransformationTracker): Normalizer = {
    new Normalizer(tracker)
  }
}
