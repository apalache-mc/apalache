package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.standard.{FlatLanguagePred, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import javax.inject.Singleton

import scala.math.BigInt

/**
 * <p>An optimizer of KerA+ expressions.</p>
 *
 * @author Igor Konnov
 */
@Singleton
class ExprOptimizer(nameGen: UniqueNameGenerator, tracker: TransformationTracker)
    extends AbstractTransformer(tracker) with TlaExTransformation {

  override val partialTransformers = List(transformFuns, transformSets, transformCard, transformExistsOverSets)

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
    case OperEx(TlaFunOper.app, OperEx(TlaFunOper.enum, ctorArgs @ _*), ValEx(TlaStr(accessedKey))) =>
      val rewrittenArgs = ctorArgs map transform
      val found = rewrittenArgs.grouped(2).find { case Seq(ValEx(TlaStr(key)), _) =>
        key == accessedKey
      }
      found match {
        case Some(pair) => pair(1) // get the value
        case _          => throw new IllegalArgumentException(s"Access to non-existent record field $accessedKey")
      }
  }

  /**
   * Set transformations.
   *
   * @return a transformed expression
   */
  private def transformSets: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaSetOper.in, mem, OperEx(TlaArithOper.dotdot, left, right)) =>
      // Transform e \in a..b into a <= e /\ e <= b.
      // (The assignments are not affected by this transformation, as they are transformed to \E t \in S: x' = t.)
      tla.and(tla.le(left, mem), tla.le(mem, right))
  }

  /**
   * Cardinality transformations.
   *
   * @return a transformed expression
   */
  private def transformCard: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaOper.eq, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal))) if intVal == BigInt(0) =>
      // Cardinality(Set) = 0, that is, Set = {}.
      // Rewrite it into \A t1 \in Set: FALSE.
      // If Set = {}, then the conjunction over the empty set is true.
      // If Set /= {}, then at least one element of Set reports FALSE, and the conjunction is false.
      // The reason why we are not rewriting it to Set = {} is that type inference would fail.
      tla.forall(tla.name(nameGen.newName()), set, tla.bool(false))

    case OperEx(TlaArithOper.gt, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal)))
        if intVal == BigInt(0) =>
      // We can find this pattern in real TLA+ benchmarks more often than one would think.
      // Rewrite into \E t1 \in set: TRUE
      tla.exists(tla.name(nameGen.newName()), set, tla.bool(true))

    case OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal)))
        if intVal == BigInt(1) =>
      // same as above
      tla.exists(tla.name(nameGen.newName()), set, tla.bool(true))

    case OperEx(TlaOper.ne, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal))) if intVal == BigInt(0) =>
      // same as above
      tla.exists(tla.name(nameGen.newName()), set, tla.bool(true))

    case OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal)))
        if intVal == BigInt(2) =>
      // We can find this pattern in real TLA+ benchmarks more often than one would think.
      // Rewrite into LET T3 = set IN \E t1 \in T3: \E t2 \in T3: t1 /= t2.
      // We use let to save on complex occurrences of set.
      val tmp1 = nameGen.newName()
      val tmp2 = nameGen.newName()
      val setName = nameGen.newName()
      val letApp = tla.appOp(NameEx(setName))
      tla.letIn(
          tla.exists(tla.name(tmp1), letApp,
              tla.exists(tla.name(tmp2), letApp, tla.not(tla.eql(tla.name(tmp1), tla.name(tmp2))))),
          TlaOperDecl(setName, List(), set)
      ) ///

    // these rewriting rules are implemented more efficiently in CardinalityConstRule.
    /*
    case OperEx(TlaArithOper.lt, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal)))
      if intVal.isValidInt =>
      val k = intVal.toInt
      // introduce k universals that have at least two equal values
      val allNames = 1.to(k).map(_ => NameEx(nameGen.newName())).toList
      val boundSetAlias = nameGen.newName()
      val boundLetApp = tla.appOp(NameEx(boundSetAlias))
      val x = NameEx(nameGen.newName())
      val y = NameEx(nameGen.newName())
      val setAlias = nameGen.newName()
      val letApp = tla.appOp(NameEx(setAlias))
      val existsEq =
        tla.exists(x, boundLetApp,
          tla.exists(y, boundLetApp,
            tla.eql(x, y)))
      val letInExistsEq =
        tla.letIn(
          existsEq,
          TlaOperDecl(boundSetAlias, List(), tla.enumSet(allNames: _*)))

      def mkForAll(underlying: TlaEx, names: Seq[NameEx]): TlaEx = {
        names match {
          case Nil => underlying
          case varName :: tl => tla.forall(varName, letApp, mkForAll(underlying, tl))
        }
      }

      tla.letIn(
        mkForAll(letInExistsEq, allNames),
        TlaOperDecl(setAlias, List(), set)
      ) ///
     */

    case OperEx(TlaArithOper.gt, card @ OperEx(TlaFiniteSetOper.cardinality, _), ValEx(TlaInt(intVal)))
        if intVal.isValidInt =>
      // Cardinality(S) > k becomes Cardinality(S) >= k + 1
      transformCard(tla.ge(card, tla.int(intVal.toInt + 1)))
  }

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
      val pairs = varsAndSets.grouped(2).toSeq.collect { case Seq(NameEx(name), set) =>
        (name, set)
      }

      // create an exists-expression and optimize it again
      def mkExistsRec(name: String, set: TlaEx, pred: TlaEx): TlaEx = {
        val exists = tla.exists(tla.name(name), set, pred)
        transformExistsOverSets.applyOrElse(exists, { _: TlaEx => exists }) // apply recursively, to optimize more
      }

      pairs.foldLeft(letIn) { case (exprBelow, (name, set)) => mkExistsRec(name, set, exprBelow) }

    // TODO: add other kinds of sets?
  }
}

object ExprOptimizer {
  def apply(uniqueNameGenerator: UniqueNameGenerator, tracker: TransformationTracker): ExprOptimizer = {
    new ExprOptimizer(uniqueNameGenerator, tracker)
  }
}
