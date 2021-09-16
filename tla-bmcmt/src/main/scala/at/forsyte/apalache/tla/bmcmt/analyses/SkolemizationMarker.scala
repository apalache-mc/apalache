package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaInt
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * <p>The skolemization analysis finds the existential quantifiers that can be safely replaced by constants
 * (Skolemizable). This class is not a pure analysis but a transformer, that is, it modifies an argument expression.
 * Additionally, this analysis finds the cardinality comparisons like Cardinality(S) >= 4 that can be checked
 * more optimally than the direct computation of the cardinalities.</p>
 *
 * <p>The previous version of this class was storing the identifiers of the Skolemizable expressions.
 * This had two disadvantages: (1) the code carried around the respective analysis store, and (2) the Skolemizable
 * expressions were not visible to the user in the intermediate output. By wrapping Skolemizable expressions
 * with skolemExists, we solve the problem more elegantly.</p>
 *
 * @author Igor Konnov
 */
class SkolemizationMarker @Inject() (tracker: TransformationTracker) extends TlaExTransformation with LazyLogging {
  override def apply(e: TlaEx): TlaEx = {
    transform(e)
  }

  def transform: TlaExTransformation = tracker.trackEx {
    case ex @ OperEx(TlaBoolOper.exists, name, set, pred) =>
      val tag = ex.typeTag
      OperEx(ApalacheOper.skolem, OperEx(TlaBoolOper.exists, name, set, transform(pred))(tag))(tag)

    case ex @ OperEx(TlaBoolOper.forall, name, set, pred) =>
      // it is fine to skolemize existentials under \A, as \A is translated into a conjunction
      OperEx(TlaBoolOper.forall, name, set, transform(pred))(ex.typeTag)

    case op @ OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, _), ValEx(TlaInt(intVal)))
        if intVal.isValidInt =>
      // this constraint can be solved more efficiently than the direct computation of Cardinality
      OperEx(ApalacheOper.constCard, op)(op.typeTag)

    case ex @ OperEx(TlaBoolOper.not, _) =>
      ex // stop here. This should be a leaf (and rare) expression, as we are dealing with the NNF.

    case ex @ OperEx(TlaBoolOper.and, args @ _*) =>
      OperEx(TlaBoolOper.and, args map transform: _*)(ex.typeTag)

    case ex @ OperEx(TlaBoolOper.or, args @ _*) =>
      OperEx(TlaBoolOper.or, args map transform: _*)(ex.typeTag)

    case ex @ OperEx(TlaControlOper.ifThenElse, cond, left, right) =>
      // try to identify existentials in the both arms
      OperEx(TlaControlOper.ifThenElse, cond, transform(left), transform(right))(ex.typeTag)
    // We omit skolemization of the existentials in the predicate,
    // as the predicate is used in both the negated and non-negated forms.
    // Effectively, IF-THEN-ELSE requires both \E and \A forms

    case ex @ LetInEx(body, defs @ _*) =>
      // At this point, we only have nullary let-in definitions of the form: `LET A == e1 in e2`
      //
      // There are two important cases to distinguish (bugfix for #985):
      //   1. Expression e1 contains `\E x \in S: P` and `A` is used in a positive form in `e2` (as a non-value).
      //   2. Expression e1 contains `\E x \in S: P` and `A` is used in a negative form or as a value in `e2`.
      //
      // Hence, we create copies of A for the both cases: one that could be skolemized and one that could not be.
      def skolemizeDef(df: TlaOperDecl): Option[TlaOperDecl] = {
        df.typeTag match {
          case Typed(OperT1(Seq(), BoolT1())) =>
            // Only if the let-definition returns a Boolean value, we have to worry about skolemization
            Some(df.copy(body = transform(df.body), name = mkSkolemName(df.name)))

          case _ =>
            None
        }

      }

      // introduce skolemized copies of the operators that return a Boolean, if needed
      LetInEx(transform(body), defs ++ defs.flatMap(skolemizeDef): _*)(ex.typeTag)

    case ex @ OperEx(TlaOper.apply, nm @ NameEx(operName)) =>
      // An application of a let-definition. As Skolemization is allowed in this context,
      // we should use the Skolemizable version of the let-definition.
      OperEx(TlaOper.apply, NameEx(mkSkolemName(operName))(nm.typeTag))(ex.typeTag)

    case ex @ OperEx(_, _ @_*) =>
      // bugfix for #148: do not descend into value expressions, as Skolemization of non-formulas is unsound
      ex

    case terminal =>
      terminal // terminal expression, stop here
  }

  private def mkSkolemName(name: String): String = {
    "%s$_skolem".format(name)
  }

}
