package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred
import javax.inject.Singleton

/**
  * <p>A simplifier from TLA+ to KerA+. This transformation assumes that all operator definitions and internal
  * let-definitions have been inlined.</p>
  *
  * <p>To get the idea about KerA+, check the paper at OOPSLA'19: TLA+ Model Checking Made Symbolic.<p>
  *
  * @author Igor Konnov
  */
@Singleton
class Keramelizer(gen: UniqueNameGenerator, tracker: TransformationTracker)
    extends AbstractTransformer(tracker) with TlaExTransformation {

  override val partialTransformers = List(transformSets)


  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  /**
    * Do set transformations.
    *
    * @return a transformed set expression
    */
  private def transformSets: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaSetOper.cap, setX, setY) =>
      val tempName = NameEx(gen.newName())
      tla.filter(tempName, setX, tla.in(tempName, setY))

    case OperEx(TlaSetOper.setminus, setX, setY) =>
      val tempName = NameEx(gen.newName())
      tla.filter(tempName, setX, tla.not(tla.in(tempName, setY)))
  }
}

object Keramelizer {
  def apply(gen: UniqueNameGenerator, tracker: TransformationTracker): Keramelizer = {
    new Keramelizer(gen, tracker)
  }
}
