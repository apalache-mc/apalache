package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaStr
import javax.inject.Singleton

/**
  * <p>An optimizer of KerA+ expressions.</p>
  *
  * @author Igor Konnov
  */
@Singleton
class ExprOptimizer(tracker: TransformationTracker)
  extends AbstractTransformer(tracker) with TlaExTransformation {

  override val partialTransformers = List(transformFuns)

  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  /**
    * Function transformations.
    *
    * @return a transformed fun expression
    */
  private def transformFuns: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaFunOper.app, OperEx(TlaFunOper.enum, ctorArgs@_*), ValEx(TlaStr(accessedKey))) =>
      val rewrittenArgs = ctorArgs map transform
      val found = rewrittenArgs.grouped(2).find {
        case Seq(ValEx(TlaStr(key)), _) => key == accessedKey
      }
      found match {
        case Some(pair) => pair(1) // get the value
        case _ => throw new IllegalArgumentException(s"Access to non-existent record field $accessedKey")
      }
  }
}

object ExprOptimizer {
  def apply(tracker: TransformationTracker): ExprOptimizer = {
    new ExprOptimizer(tracker)
  }
}

