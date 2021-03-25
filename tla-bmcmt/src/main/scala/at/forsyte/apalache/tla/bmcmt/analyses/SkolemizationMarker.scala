package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
 * <p>The skolemization analysis finds the existential quantifiers that can be safely replace by constants
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
      // at this point, we only have nullary let-in definitions
      def mapDef(df: TlaOperDecl) = df.copy(body = transform(df.body))

      LetInEx(transform(body), defs map mapDef: _*)(ex.typeTag)

    case ex @ OperEx(oper, args @ _*) =>
      // bugfix for #148: do not descend into value expressions, as Skolemization of non-formulas is unsound
      ex

    case terminal =>
      terminal // terminal expression, stop here
  }

}
