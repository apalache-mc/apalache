package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.standard.{DeepCopy, FlatLanguagePred, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import TypedPredefs._

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

  private val boolTag = Typed(BoolT1())
  private val intTag = Typed(IntT1())

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
      tla
        .and(tla.le(left, mem) ? "b", tla.le(mem, right) ? "b")
        .typed(Map("b" -> BoolT1()), "b")
  }

  /**
   * Cardinality transformations.
   *
   * @return a transformed expression
   */
  private def transformCard: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaOper.eq, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal))) if intVal == BigInt(0) =>
      // Cardinality(Set) = 0, that is, Set = {}.
      // Rewrite it to Set = {}, as its complexity is lower.
      // Thanks to the type tags, we can simply carry the set type to the empty set.
      OperEx(TlaOper.eq, set, OperEx(TlaSetOper.enumSet)(set.typeTag))(boolTag)

    case OperEx(TlaArithOper.gt, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal)))
        if intVal == BigInt(0) =>
      // Cardinality(S) > 0, that is, Set /= {}.
      // We can find this pattern in real TLA+ benchmarks more often than one would think.
      OperEx(TlaBoolOper.not, OperEx(TlaOper.eq, set, OperEx(TlaSetOper.enumSet)(set.typeTag))(boolTag))(boolTag)

    case OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal)))
        if intVal == BigInt(1) =>
      // Cardinality(S) >= 1, that is, Set /= {}.
      OperEx(TlaBoolOper.not, OperEx(TlaOper.eq, set, OperEx(TlaSetOper.enumSet)(set.typeTag))(boolTag))(boolTag)

    case OperEx(TlaOper.ne, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal))) if intVal == BigInt(0) =>
      // Cardinality(S) /= 0, that is, Set /= {}.
      OperEx(TlaBoolOper.not, OperEx(TlaOper.eq, set, OperEx(TlaSetOper.enumSet)(set.typeTag))(boolTag))(boolTag)

    case OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, set), ValEx(TlaInt(intVal)))
        if intVal == BigInt(2) =>
      // Cardinality(Set) >= 2.
      // We can find this pattern in real TLA+ benchmarks more often than one would think.
      // Rewrite into LET T3 = set IN \E t1 \in T3: \E t2 \in T3: t1 /= t2.
      // We use let to save on complex occurrences of set.
      val elemType = set.typeTag match {
        case Typed(SetT1(et)) => et
        case _                =>
          // this should never happen as the type checker ensures that types are correct
          throw new TypingException("Unexpected type %s in expression %s".format(set.typeTag, set))
      }

      def mkElemName(name: String): TlaEx = {
        NameEx(name)(Typed(elemType))
      }

      val tmp1 = nameGen.newName()
      val tmp2 = nameGen.newName()
      val letDefName = nameGen.newName()
      val operType = OperT1(Seq(), SetT1(elemType))
      val letDef = TlaOperDecl(letDefName, List(), set)(Typed(operType))
      val applyLet = OperEx(TlaOper.apply, NameEx(letDefName)(Typed(operType)))(set.typeTag)

      def exists(name: String, pred: TlaEx) = {
        OperEx(TlaBoolOper.exists, NameEx(name)(Typed(elemType)), applyLet, pred)(boolTag)
      }

      val test = OperEx(TlaBoolOper.not, OperEx(TlaOper.eq, mkElemName(tmp1), mkElemName(tmp2))(boolTag))(boolTag)

      LetInEx(exists(tmp1, exists(tmp2, test)), letDef)(boolTag)

    // the more general case Cardinality(S) >= k, for a constant k, is implemented more efficiently in CardinalityConstRule.

    case OperEx(TlaArithOper.gt, card @ OperEx(TlaFiniteSetOper.cardinality, _), ValEx(TlaInt(intVal)))
        if (intVal + 1).isValidInt =>
      // Cardinality(S) > k becomes Cardinality(S) >= k + 1
      val kPlus1 = ValEx(TlaInt((intVal + 1).toInt))(intTag)
      val ge = OperEx(TlaArithOper.ge, card, kPlus1)(boolTag)
      transformCard(ge)
  }

  /**
   * Transformations for existential quantification over sets: \exists x \in SetExpr: P.
   *
   * @return a transformed \exists expression
   */
  private def transformExistsOverSets: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaBoolOper.exists, xe @ NameEx(x), OperEx(TlaSetOper.filter, ye @ NameEx(y), s, e), g) =>
      // \E x \in {y \in S: e}: g becomes \E y \in S: e /\ g [x replaced with y]
      val eAndG = tla.and(e, g).typed(BoolT1())
      val newPred =
        ReplaceFixed(tracker)(replacedEx = xe, newEx = NameEx(y)(ye.typeTag)).apply(eAndG)
      val result = OperEx(TlaBoolOper.exists, NameEx(y)(ye.typeTag), s, newPred)(boolTag)
      transformExistsOverSets.applyOrElse(result, { _: TlaEx => result }) // apply recursively to the result

    case OperEx(TlaBoolOper.exists, xe @ NameEx(_), OperEx(TlaSetOper.map, mapEx, varsAndSets @ _*), pred) =>
      // e.g., \E x \in {e: y \in S}: g becomes \E y \in S: g[x replaced with e]
      // g[x replaced with e] in the example above
      val newPred = ReplaceFixed(tracker)(replacedEx = xe, newEx = DeepCopy(tracker).deepCopyEx(mapEx)).apply(pred)

      // \E y \in S: ... in the example above
      val pairs = varsAndSets.grouped(2).toSeq.collect { case Seq(NameEx(name), set) =>
        (name, set)
      }

      // create an exists-expression and optimize it again
      def mkExistsRec(name: String, set: TlaEx, pred: TlaEx): TlaEx = {
        val elemType = getElemType(set)
        val exists = tla
          .exists(tla.name(name) ? "e", set, pred)
          .typed(Map("e" -> elemType, "b" -> BoolT1()), "b")
        transformExistsOverSets.applyOrElse(exists, { _: TlaEx => exists }) // apply recursively, to optimize more
      }

      pairs.foldLeft(newPred) { case (exprBelow, (name, set)) => mkExistsRec(name, set, exprBelow) }

    // TODO: add other kinds of sets?
  }

  // extract the type of a set element
  private def getElemType(e: TlaEx): TlaType1 = {
    e.typeTag match {
      case Typed(SetT1(elemType)) => elemType
      case t =>
        throw new MalformedTlaError(s"Expected a set, found: $t", e)
    }
  }
}

object ExprOptimizer {
  def apply(uniqueNameGenerator: UniqueNameGenerator, tracker: TransformationTracker): ExprOptimizer = {
    new ExprOptimizer(uniqueNameGenerator, tracker)
  }
}
