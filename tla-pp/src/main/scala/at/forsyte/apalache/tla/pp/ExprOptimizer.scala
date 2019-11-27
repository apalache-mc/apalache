package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.standard.{FlatLanguagePred, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaStr
import javax.inject.Singleton

/**
  * <p>An optimizer of KerA+ expressions.</p>
  *
  * @author Igor Konnov
  */
@Singleton
class ExprOptimizer(nameGen: UniqueNameGenerator, tracker: TransformationTracker)
  extends AbstractTransformer(tracker) with TlaExTransformation {

  override val partialTransformers = List(transformFuns, transformExistsOverSets)

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

  // TODO: add unit tests

  /**
    * Transformations for existential quantification over sets: \exists x \in SetExpr: P.
    *
    * @return a transformed \exists expression
    */
  private def transformExistsOverSets: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaBoolOper.exists, NameEx(x), OperEx(TlaSetOper.filter, NameEx(y), s, e), g) =>
      // \E x \in {y \in S: e}: g becomes \E y \in S: e /\ g [x replaced with y]
      val newPred = ReplaceFixed(NameEx(x), NameEx(y), tracker).apply(tla.and(e, g))
      val result = tla.exists(tla.name(y), s, newPred)
      transformExistsOverSets.applyOrElse(result, { _: TlaEx => result }) // apply recursively to the result

    case OperEx(TlaBoolOper.exists, NameEx(boundVar), OperEx(TlaSetOper.map, mapEx, varsAndSets @ _*), pred) =>
      // e.g., \E x \in {e: y \in S}: g becomes \E y \in S: LET tmp == e IN g [x replaced with e]
      // LET x == e IN g in the example above
      val letName = nameGen.newName()
      val newPred = ReplaceFixed(NameEx(boundVar), tla.appOp(NameEx(letName)), tracker).apply(pred)

      val letIn: TlaEx = LetInEx(newPred, TlaOperDecl(letName, List(), mapEx))
      // \E y \in S: ... in the example above
      val pairs = varsAndSets.grouped(2).collect {
        case NameEx(name) :: set :: _ => (name, set)
      }
      // create an exists-expression and optimize it again
      def mkExistsRec(name: String, set: TlaEx, pred: TlaEx): TlaEx = {
        val exists = tla.exists(tla.name(name), set, pred)
        transformExistsOverSets.applyOrElse(exists, { _: TlaEx => exists }) // apply recursively, to optimize more
      }

      pairs.foldLeft(letIn) { case (exprBelow, (name, set)) => mkExistsRec(name, set, exprBelow) }

      // TODO: add other kinds of sets
  }
}

object ExprOptimizer {
  def apply(uniqueNameGenerator: UniqueNameGenerator, tracker: TransformationTracker): ExprOptimizer = {
    new ExprOptimizer(uniqueNameGenerator, tracker)
  }
}

