package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaFunOper}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
 * Transforms UNCHANGED x, by flattening it once.
 *
 * `UNCHANGED x` becomes `x' = x`
 *
 * `UNCHANGED <<x, y>>` becomes `x' = x /\ y' = y`
 *
 * `UNCHANGED <<x, <<y,z>>>>` is rejected
 *
 * Desugarer also performs the same transformation, however, it performs additional transformations not desired in the
 * VMT translation process.
 *
 * TODO: See #1422
 *
 * @author
 *   Jure Kukovec
 */
class SimpleUnchangedUnroller(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(ex: TlaEx): TlaEx = transform(ex)

  private def mkPrimeEq(ex: TlaEx): TlaEx = {
    val t = ex.typeTag.asTlaType1()
    tla.eql(tla.prime(ex.copy()).as(t), ex.copy()).as(BoolT1)
  }

  private def transform: TlaExTransformation = tracker.trackEx {
    case OperEx(TlaActionOper.unchanged, arg) =>
      arg match {
        case OperEx(TlaFunOper.tuple, args @ _*) =>
          tla.and(args.map(mkPrimeEq): _*).as(BoolT1)
        case _ => mkPrimeEq(arg)
      }
    // we can skip
    // case LetInEx(body, decls @ _*) => ...
    // because this must run AFTER inlining for reTLA, which removes all let-ins

    case ex @ OperEx(oper, args @ _*) =>
      val newArgs = args.map(transform)
      if (args == newArgs) ex else OperEx(oper, newArgs: _*)(ex.typeTag)

    case ex =>
      ex
  }
}

object SimpleUnchangedUnroller {
  def apply(transformationTracker: TransformationTracker): SimpleUnchangedUnroller =
    new SimpleUnchangedUnroller(transformationTracker)
}
