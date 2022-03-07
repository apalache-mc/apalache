package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TransformationTracker}
import at.forsyte.apalache.tla.lir.values._

/**
 * A simplifier that rewrites expressions commonly found in `TypeOK`. Assumes expressions to be well-typed.
 *
 * After Apalache's type-checking, we can rewrite some expressions to simpler forms. For example, the (after
 * type-checking) vacuously true `x \in BOOLEAN` is rewritten to `TRUE` (as `x` must be a `BoolT1`).
 *
 * We currently perform the following simplifications (for applicable sets AS, see [[isApplicable]]):
 *   - `n \in Nat` ~> `x >= 0`
 *   - `b \in BOOLEAN`, `i \in Int`, `r \in Real` ~> `TRUE`
 *   - `seq \in Seq(AS)` ~> `TRUE`
 *   - `set \in SUBSET AS` ~> `TRUE`
 *   - `fun \in [AS1 -> AS2]` ~> `TRUE`
 *   - `fun \in [Dom -> AS]` ~> `DOMAIN fun = Dom`
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
   * Returns true iff rewriting of a well-typed set-membership test `x \in arg` to `TRUE` is applicable for the
   * function's argument.
   *
   * The applicable sets are inductively defined as
   *   - the predefined sets BOOLEAN, Int, Real, STRING,
   *   - sets of sequences over applicable sets, e.g., Seq(BOOLEAN), Seq(Int), Seq(Seq(Int)), Seq(SUBSET Int), ...
   *   - power sets of applicable sets, e.g., SUBSET BOOLEAN, SUBSET Int, SUBSET Seq(Int), ...
   *   - sets of functions over applicable sets, e.g., [Int -> BOOLEAN], ...
   *
   * In particular, it is *not* applicable to `Nat` and sequence sets / power sets thereof, since `i \in Nat` does not
   * hold for all `IntT1`-typed `i`.
   */
  private def isApplicable: Function[TlaEx, Boolean] = {
    // base case: BOOLEAN, Int, Real, STRING
    case ValEx(TlaBoolSet) | ValEx(TlaIntSet) | ValEx(TlaRealSet) | ValEx(TlaStrSet) => true

    // inductive cases:
    // 1. Seq(s) for applicable set `s`
    case OperEx(TlaSetOper.seqSet, set) => isApplicable(set)
    // 2. SUBSET s for applicable set `s`
    case OperEx(TlaSetOper.powerset, set) => isApplicable(set)
    // 3. [s1 -> s2] for applicable sets `s1` and `s2
    case OperEx(TlaSetOper.funSet, set1, set2) => isApplicable(set1) && isApplicable(set2)

    // otherwise
    case _ => false
  }

  /**
   * Simplifies expressions commonly found in `TypeOK`, assuming they are well-typed.
   *
   * @see
   *   [[SetMembershipSimplifier]] for a full list of supported rewritings.
   */
  private def transformMembership: PartialFunction[TlaEx, TlaEx] = {
    // n \in Nat  ~>  x >= 0
    case OperEx(TlaSetOper.in, name, ValEx(TlaNatSet)) =>
      OperEx(TlaArithOper.ge, name, ValEx(TlaInt(0))(intTag))(boolTag)

    /* For ApplicableSets AS (see `isApplicable`): */

    // x \in AS  ~>  TRUE
    case OperEx(TlaSetOper.in, _, set) if isApplicable(set) => trueVal

    // fun \in [Dom -> AS]  ~>  DOMAIN fun = Dom    (fun \in [AS1 -> AS2] is handled above)
    case OperEx(TlaSetOper.in, fun, OperEx(TlaSetOper.funSet, domain, set2)) if isApplicable(set2) =>
      OperEx(TlaOper.eq, OperEx(TlaFunOper.domain, fun)(domain.typeTag), domain)(boolTag)

    // otherwise, return `ex` unchanged
    case ex => ex
  }
}

object SetMembershipSimplifier {
  def apply(tracker: TransformationTracker): SetMembershipSimplifier = new SetMembershipSimplifier(tracker)
}
