package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations._

/**
 * LetInApplier turns applications of operator-typed LET-expressions, into LET-expressions with applications pushed into
 * the body.
 *
 * Workaround until LAMBDAS are systematically supported (#2534).
 *
 * @author
 *   Jure Kukovec
 */
class LetInApplier(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(input: TlaEx): TlaEx = {
    transform(input)
  }

  private def transform: TlaExTransformation = tracker.trackEx {
    case ex @ OperEx(TlaOper.apply, LetInEx(nameEx @ NameEx(operName), decl @ TlaOperDecl(declName, _, _)), args @ _*)
        if operName == declName =>
      LetInEx(
          OperEx(TlaOper.apply, nameEx +: args.map(transform): _*)(ex.typeTag),
          decl.copy(body = transform(decl.body)),
      )(ex.typeTag)

    case ex @ _ => ex
  }
}
