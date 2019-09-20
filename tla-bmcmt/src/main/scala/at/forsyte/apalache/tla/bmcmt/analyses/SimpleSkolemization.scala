package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaControlOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
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
class SimpleSkolemization @Inject()(
                                     val frexStore: FreeExistentialsStoreImpl,
                                     tracker: TransformationTracker
                                   ) extends LazyLogging {
  /**
    * Transform the transitions into normal form and label the free existential quantifiers.
    *
    * @param spec a specification with identified transitions
    * @return the modified input
    */
  def transformAndLabel( decls: Traversable[TlaOperDecl] ) : Traversable[TlaOperDecl] = decls map { d =>
    val newBody = toNegatedForm( d.body )
    markFreeExistentials( newBody )
    d.copy( body = newBody )
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

  private def toNegatedForm : TlaExTransformation = tracker.track { rootExpr =>
    def nnf(neg: Boolean) : TlaExTransformation = tracker.track {
      case ValEx(TlaBool(b)) =>
        tla.bool(b ^ neg)

      case ex@ValEx(_) =>
        throw new RewriterException("Negation should not propagate to a non-boolean constant: " + ex)

      case ex@NameEx(_) =>
        if (neg) tla.not(ex) else ex

      case OperEx(TlaBoolOper.not, arg) =>
        nnf(!neg)(arg)

      case ite@OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        // ~ITE(A, B, C) == ITE(A, ~B, ~C)
        val recNnf = nnf(neg)
        OperEx(TlaControlOper.ifThenElse, predEx, recNnf(thenEx), recNnf(elseEx))

      case OperEx(TlaBoolOper.and, args@_*) =>
        val oper = if (neg) TlaBoolOper.or else TlaBoolOper.and
        OperEx(oper, args map nnf(neg): _*)

      case OperEx(TlaBoolOper.or, args@_*) =>
        val oper = if (neg) TlaBoolOper.and else TlaBoolOper.or
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
        OperEx(TlaOper.label, nnf(neg)(subex) +: args: _*)

      case LetInEx(body, defs @ _*) =>

        /**
          * To handle the case of LET X == ... IN ... ~X ...
          * we introduce a new let-in operator NegX$, the body of which is the
          * nnf transformation of the body of X. Then, we replace all calls to ~X in the
          * LET-IN body with calls to NegX$.
          */

        def negName( n: String ): String = s"Neg$n$$"

        val newBody = nnf( neg )( body )

        // We can't just implement ~X for all operators ( e.g. what if X == 1..10 ), just for
        // those that actually appear under negation in the body (and thus must be of type Bool)
        def negAppearingOpers( tlaEx : TlaEx ) : Set[String] = tlaEx match {
          case OperEx( TlaBoolOper.not, OperEx( TlaOper.apply, NameEx( name ) ) ) =>
            Set(name)
          case OperEx( op, args@_* ) =>
            args.map( negAppearingOpers ).foldLeft( Set.empty[String] ) {
              _ ++ _
            }
          case LetInEx( b, ds@_* ) =>
            ds.map( d => negAppearingOpers( d.body ) ).foldLeft( negAppearingOpers( b ) ) {
              _ ++ _
            }
          case _ => Set.empty[String]
        }

        val negOpers = negAppearingOpers( newBody )

        val replacements = negOpers map { opName =>
          ReplaceFixed(
            OperEx( TlaBoolOper.not, OperEx( TlaOper.apply, NameEx( opName ) ) ),
            OperEx( TlaOper.apply, NameEx( negName( opName ) ) ),
            tracker
          )
        }

        val negReplacedBody = replacements.foldLeft( newBody ) { case (b, tr) =>
          tr( b )
        }

        val negDefs = defs withFilter { d => negOpers.contains( d.name ) } map { d =>
          d.copy( name = negName( d.name ), body = nnf( neg = true )( d.body ) )
        }

        val newDefs = defs ++ negDefs

        LetInEx( negReplacedBody, newDefs : _ * )

      case ex =>
        if (!neg)
          ex
        else OperEx(TlaBoolOper.not, ex)
    }
    nnf(neg = false)(rootExpr)
  }
}
