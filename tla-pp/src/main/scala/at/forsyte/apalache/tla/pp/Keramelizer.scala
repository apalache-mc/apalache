package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import TypedPredefs._

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
    List(transformLogic, transformSets, transformTuples, transformRecords, transformControl, transformAssignments)

  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  // extract the type of a set element
  private def getElemType(e: TlaEx): TlaType1 = {
    e.typeTag match {
      case Typed(SetT1(elemType)) => elemType
      case t =>
        throw new MalformedTlaError(s"Expected a set, found: $t", e)
    }
  }

  /**
   * Set transformations.
   *
   * @return a transformed set expression
   */
  private def transformSets: PartialFunction[TlaEx, TlaEx] = {
    case ex @ OperEx(TlaSetOper.cap, setX, setY) =>
      val elemType = getElemType(setX)
      val tempName = gen.newName()
      tla
        .filter(tla.name(tempName) ? "e", setX, tla.in(tla.name(tempName) ? "e", setY) ? "b")
        .typed(Map("b" -> BoolT1(), "e" -> elemType, "s" -> SetT1(elemType)), "s")

    case ex @ OperEx(TlaSetOper.setminus, setX, setY) =>
      val elemType = getElemType(setX)
      val tempName = gen.newName()
      tla
        .filter(tla.name(tempName) ? "e", setX, tla.not(tla.in(tla.name(tempName) ? "e", setY) ? "b") ? "b")
        .typed(Map("b" -> BoolT1(), "e" -> elemType, "s" -> SetT1(elemType)), "s")

    case OperEx(TlaSetOper.notin, x, setX) =>
      tla
        .not(tla.in(x, setX) ? "b")
        .typed(Map("b" -> BoolT1()), "b")
  }

  /**
   * Record transformations.
   *
   * @return a transformed expression
   */
  private def transformRecords: PartialFunction[TlaEx, TlaEx] = {
    case ex @ OperEx(TlaSetOper.recSet, keysAndSets @ _*) =>
      // rewrite [ k_1: S_1, ..., k_n: S_n ]
      // into { y_1 \in S_1, ..., y_n \in S_n: [ k_1 |-> y_1, ..., k_n |-> y_n ] }
      val (keys, sets) = TlaOper.deinterleave(keysAndSets)
      val elemTypes = sets map getElemType
      // produce a sequence of fresh names wrapped with NameEx
      val names: Seq[TlaEx] = elemTypes map { t => NameEx(gen.newName())(Typed(t)) }
      val keysAndNamesInterleaved = TlaOper.interleave(keys, names)
      val recordType = getElemType(ex)
      // [ x_1 |-> v_1, ..., x_n |-> v_n ]
      val mapEx = OperEx(TlaFunOper.enum, keysAndNamesInterleaved: _*)(Typed(recordType))
      // { y_1 \in S_1, ..., y_n \in S_n: [ k_1 |-> y_1, ..., k_n |-> y_n ] }
      val namesAndSetsInterleaved = TlaOper.interleave(names, sets)
      OperEx(TlaSetOper.map, mapEx +: namesAndSetsInterleaved: _*)(ex.typeTag)
  }

  /**
   * Tuple transformations.
   *
   * @return a transformed expression
   */
  private def transformTuples: PartialFunction[TlaEx, TlaEx] = { case ex @ OperEx(TlaSetOper.times, sets @ _*) =>
    // transform S_1 \X ... \X S_n
    // into { y_1 \in S_1, ..., y_n \in S_n: <<y_1, ..., y_n>> }
    val elemTypes = sets map getElemType
    val names: Seq[TlaEx] = elemTypes.map(t => NameEx(gen.newName())(Typed(t)))
    val mapEx = OperEx(TlaFunOper.tuple, names: _*)(Typed(TupT1(elemTypes: _*)))
    val namesAndSets = TlaOper.interleave(names, sets)
    OperEx(TlaSetOper.map, mapEx +: namesAndSets: _*)(ex.typeTag)
  }

  /**
   * Boolean equivalences.
   *
   * @return a transformed expression
   */
  private def transformLogic: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaBoolOper.equiv, left, right) =>
      tla.eql(left, right) typed BoolT1()

    case OperEx(TlaBoolOper.implies, left, right) =>
      tla
        .or(tla.not(left) ? "b", right)
        .typed(Map("b" -> BoolT1()), "b")

    case OperEx(TlaOper.ne, left, right) =>
      tla
        .not(tla.eql(left, right) ? "b")
        .typed(Map("b" -> BoolT1()), "b")
  }

  /**
   * Assignment-like expressions.
   *
   * @return a transformed expression
   */
  private def transformAssignments: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaSetOper.in, prime @ OperEx(TlaActionOper.prime, NameEx(x)), set) =>
      // rewrite x' \in S
      // into \E y \in S: x' = y
      val elemType = getElemType(set)
      val temp = gen.newName()
      tla
        .exists(tla.name(temp) ? "e", set, tla.eql(prime, tla.name(temp) ? "e") ? "b")
        .typed(Map("b" -> BoolT1(), "e" -> elemType), "b")
  }

  /**
   * Control flow transformations.
   *
   * @return a transformed expression
   */
  private def transformControl: PartialFunction[TlaEx, TlaEx] = {

    case expr @ OperEx(TlaControlOper.caseWithOther, otherEx, args @ _*) =>
      // CASE with a default arm
      if (expr.typeTag == Typed(BoolT1())) {
        // the Boolean case becomes a disjunction that has otherEx as an option
        val (guards, actions) = TlaOper.deinterleave(args)
        // produce g_1 /\ a_1, ..., g_n /\ a_n
        val ands = guards.zip(actions) map { case (g, a) => tla.and(g, a).typed(BoolT1()) }
        val otherForm = tla.and(guards.map(g => tla.not(g).typed(BoolT1())) :+ otherEx: _*).typed(BoolT1())
        // (g_1 /\ a_1) \/ ... \/ (g_n /\ a_n) \/ ~g_1 /\ ... /\ ~g_n /\ otherEx
        tla.or(ands :+ otherForm: _*).typed(BoolT1())
      } else {
        // produce a chain: IF g_1 THEN e_1 ELSE (IF g_2 THEN e_2 ELSE (..( ELSE otherEx)..)
        val revGuardsAndActions = mkGuardsAndActions(args)
        revGuardsAndActions.foldLeft(otherEx)(decorateWithIf)
      }

    case expr @ OperEx(TlaControlOper.caseNoOther, args @ _*) =>
      // CASE without a default arm
      if (expr.typeTag == Typed(BoolT1())) {
        // the Boolean case becomes a disjunction
        val (guards, actions) = TlaOper.deinterleave(args)
        // produce g_1 /\ a_1, ..., g_n /\ a_n
        val ands = guards.zip(actions) map { case (g, a) => tla.and(g, a).typed(BoolT1()) }
        // (g_1 /\ a_1) \/ ... \/ (g_n /\ a_n)
        tla.or(ands: _*).typed(BoolT1())
      } else {
        // produce a chain: IF g_1 THEN e_1 ELSE (IF g_2 THEN e_2 ELSE (..( ELSE e_n)..)
        if (args.length >= 2) {
          // ignore the last guard and treat lastAction as the default arm
          val prefix = args.dropRight(2)
          val revGuardsAndActions = mkGuardsAndActions(prefix)
          revGuardsAndActions.foldLeft(args.last)(decorateWithIf)
        } else {
          // in the unlikely case of CASE without any guards, just return FALSE
          tla.bool(false).typed()
        }
      }
  }

  private def decorateWithIf(elseEx: TlaEx, guardAction: (TlaEx, TlaEx)): TlaEx = {
    tla.ite(guardAction._1, guardAction._2, elseEx).typed(elseEx.typeTag.asTlaType1())
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
