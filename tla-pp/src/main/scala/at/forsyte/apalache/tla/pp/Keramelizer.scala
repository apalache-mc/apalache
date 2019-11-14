package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper._
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

  override val partialTransformers =
    List(transformLogic, transformSets, transformTuples, transformRecords, transformControl)


  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  /**
    * Set transformations.
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

    case OperEx(TlaSetOper.notin, x, setX) =>
      tla.not(tla.in(x, setX))

    case OperEx(TlaSetOper.supseteq, setX, setY) =>
      tla.subseteq(setY, setX)

    case OperEx(TlaSetOper.subsetProper, setX, setY) =>
      tla.and(
        tla.not(tla.eql(setX, setY)),
        tla.subseteq(setX, setY)
      ) ///

    case OperEx(TlaSetOper.supsetProper, setX, setY) =>
      tla.and(
        tla.not(tla.eql(setX, setY)),
        tla.subseteq(setY, setX)
      ) ///
  }

  /**
    * Record transformations.
    *
    * @return a transformed expression
    */
  private def transformRecords: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaSetOper.recSet, varsAndSets @ _*) =>
      val vars = varsAndSets.zipWithIndex.filter(_._2 % 2 == 0).map(_._1)
      val sets = varsAndSets.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
      val boundVars: Seq[TlaEx] = vars.map(_ => NameEx(gen.newName()))
      val mapEx = OperEx(TlaFunOper.enum, vars.zip(boundVars).flatMap(x => List(x._1, x._2)): _*)
      OperEx(TlaSetOper.map, mapEx +: boundVars.zip(sets).flatMap(x => List(x._1, x._2)): _*)
  }

  /**
    * Tuple transformations.
    *
    * @return a transformed expression
    */
  private def transformTuples: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaSetOper.times, sets @ _*) =>
      val boundVars: Seq[TlaEx] = sets.map(_ => NameEx(gen.newName()))
      val mapEx = OperEx(TlaFunOper.tuple, boundVars: _*)
      OperEx(TlaSetOper.map, mapEx +: boundVars.zip(sets).flatMap(x => List(x._1, x._2)): _*)
  }

  /**
    * Boolean equivalences.
    *
    * @return a transformed expression
    */
  private def transformLogic: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaBoolOper.equiv, left, right) =>
      tla.eql(left, right)

    case OperEx(TlaBoolOper.implies, left, right) =>
      tla.or(tla.not(left), right)

    case OperEx(TlaOper.ne, left, right) =>
      tla.not(tla.eql(left, right))
  }

  /**
    * Control flow transformations.
    *
    * @return a transformed expression
    */
  private def transformControl: PartialFunction[TlaEx, TlaEx] = {
    case expr @ OperEx(TlaControlOper.caseWithOther, otherEx, args @ _*) =>
      def decorateWithIf(elseEx: TlaEx, guardAction: (TlaEx, TlaEx)): OperEx = {
        tla.ite(guardAction._1, guardAction._2, elseEx)
      }
      // produce a chain of if-then-else expressions
      val revGuardsAndActions = mkGuardsAndActions(args)
      revGuardsAndActions.foldLeft(otherEx)(decorateWithIf)

    case expr @ OperEx(TlaControlOper.caseNoOther, _*) =>
      throw new NotInKeraError("CASE without other, see: " +
        "https://github.com/konnov/apalache/blob/feature/keramel/docs/preprocessing.md", expr)
  }

  private def mkGuardsAndActions(args: Seq[TlaEx]): Seq[(TlaEx, TlaEx)] = {
    assert(args.length % 2 == 0) // even
    val guards = args.zipWithIndex.filter(p => p._2 % 2 == 0).map(_._1)
    val actions = args.zipWithIndex.filter(p => p._2 % 2 != 0).map(_._1)
    guards.zip(actions).reverse
  }

}

object Keramelizer {
  def apply(gen: UniqueNameGenerator, tracker: TransformationTracker): Keramelizer = {
    new Keramelizer(gen, tracker)
  }
}
