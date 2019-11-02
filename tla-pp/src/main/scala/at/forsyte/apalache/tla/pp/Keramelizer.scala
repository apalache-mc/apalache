package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred

/**
  * <p>A simplifier from TLA+ to KerA+. This transformation assumes that all operator definitions and internal
  * let-definitions have been inlined.</p>
  *
  * <p>To get the idea about KerA+, check the paper at OOPSLA'19: TLA+ Model Checking Made Symbolic.<p>
  *
  * @author Igor Konnov
  */
class Keramelizer(gen: UniqueNameGenerator, tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  /**
    * Transform an expression recursively, by rewriting some TLA+ expressions in KerA+.
    *
    * @return a new expression
    */
  def transform: TlaExTransformation = tracker.track {
    case OperEx(op, args @ _*) =>
      transformOneLevel(OperEx(op, args map transform :_*))

    case LetInEx(body, defs @ _*) =>
      def mapDecl(d: TlaOperDecl): TlaOperDecl = {
        TlaOperDecl(d.name, d.formalParams, transform(d.body))
      }

      LetInEx(transform(body), defs.map(mapDecl) :_*)

    case ex =>
      transformOneLevel(ex)
  }

  /**
    * Transform an expression without looking into the arguments.
    * @return a new expression
    */
  private def transformOneLevel: TlaExTransformation = {
    val identity: PartialFunction[TlaEx, TlaEx] = {
      case e => e
    }
    // chain partial functions to handle different types of operators with different functions
    val handlers =
      List(
        transformSets,
        identity
      ) ///

    // and track the changes
    tracker.track(handlers reduceLeft (_ orElse _))
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
