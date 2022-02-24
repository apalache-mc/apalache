package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TransformationTracker}
import at.forsyte.apalache.tla.lir.values._

/**
 * A simplifier that rewrites vacuously true membership tests based on type information.
 *
 * For example, `x \in BOOLEAN` is rewritten to `TRUE` if x is typed BoolT1.
 *
 * @author
 *   Thomas Pani
 */
class SetMembershipSimplifier(tracker: TransformationTracker) extends AbstractTransformer(tracker) {
  private val boolTag = Typed(BoolT1())
  private def trueVal: ValEx = ValEx(TlaBool(true))(boolTag)

  override val partialTransformers = List(transformMembership)

  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  private def typeOfPredefSet: PartialFunction[TlaPredefSet, TlaType1] = {
    case TlaBoolSet => BoolT1()
    case TlaIntSet  => IntT1()
    case TlaRealSet => RealT1()
    case TlaStrSet  => StrT1()
  }

  private def matchesType(name: TlaEx, ps: TlaPredefSet): Boolean = name.typeTag == Typed(typeOfPredefSet(ps))
  private def matchesSeqType(name: TlaEx, ps: TlaPredefSet): Boolean = name.typeTag == Typed(SeqT1(typeOfPredefSet(ps)))

  private def transformMembership: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaSetOper.in, name, ValEx(ps: TlaPredefSet)) if matchesType(name, ps) => trueVal
    case OperEx(TlaSetOper.in, name, OperEx(TlaSetOper.seqSet, ValEx(ps: TlaPredefSet))) if matchesSeqType(name, ps) =>
      trueVal
    case ex => ex
  }
}

object SetMembershipSimplifier {
  def apply(tracker: TransformationTracker): SetMembershipSimplifier = new SetMembershipSimplifier(tracker)
}
