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
  private val intTag = Typed(IntT1())
  private def trueVal: ValEx = ValEx(TlaBool(true))(boolTag)

  override val partialTransformers = List(transformMembership)

  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  /**
   * Returns the type of a TLA+ predefined set, if rewriting set membership to TRUE is applicable. In particular, it is
   * *not* applicable to `Nat`, since `i \in Nat` does not hold for all `IntT1`-typed `i`.
   */
  private def typeOfSupportedPredefSet: PartialFunction[TlaPredefSet, TlaType1] = {
    case TlaBoolSet => BoolT1()
    case TlaIntSet  => IntT1()
    case TlaRealSet => RealT1()
    case TlaStrSet  => StrT1()
    // intentionally omits TlaNatSet, see above.
  }

  /**
   * Checks if this transformation is applicable (see [[typeOfSupportedPredefSet]]) to a TLA+ predefined set `ps` of
   * primitives, and if the types of `name` and `ps` match.
   */
  private def isApplicable(name: TlaEx, ps: TlaPredefSet): Boolean =
    typeOfSupportedPredefSet.isDefinedAt(ps) && name.typeTag == Typed(typeOfSupportedPredefSet(ps))

  /**
   * Checks if this transformation is applicable (see [[typeOfSupportedPredefSet]]) to a TLA+ predefined set of
   * sequences (`Seq(_)`) `ps`, and if the types of `name` and `ps` match.
   */
  private def isApplicableSeq(name: TlaEx, ps: TlaPredefSet): Boolean =
    typeOfSupportedPredefSet.isDefinedAt(ps) && name.typeTag == Typed(SeqT1(typeOfSupportedPredefSet(ps)))

  /**
   * Rewrites vacuously true membership tests based on type information, and rewrites `i \in Nat` to `i \ge 0`.
   *
   * For example, `x \in BOOLEAN` is rewritten to `TRUE` if `x` is typed `BoolT1`.
   */
  private def transformMembership: PartialFunction[TlaEx, TlaEx] = {
    case OperEx(TlaSetOper.in, name, ValEx(TlaNatSet)) if name.typeTag == Typed(IntT1()) =>
      OperEx(TlaArithOper.ge, name, ValEx(TlaInt(0))(intTag))(boolTag)
    case OperEx(TlaSetOper.in, name, ValEx(ps: TlaPredefSet)) if isApplicable(name, ps) => trueVal
    case OperEx(TlaSetOper.in, name, OperEx(TlaSetOper.seqSet, ValEx(ps: TlaPredefSet))) if isApplicableSeq(name, ps) =>
      trueVal
    case ex => ex
  }
}

object SetMembershipSimplifier {
  def apply(tracker: TransformationTracker): SetMembershipSimplifier = new SetMembershipSimplifier(tracker)
}
