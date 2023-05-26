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
 * We currently perform the following simplifications (for a definition of type-defining sets (TDS), see the private
 * method `isTypeDefining`):
 *   - `n \in Nat` ~> `x >= 0`
 *   - `b \in BOOLEAN`, `i \in Int`, `r \in Real` ~> `TRUE`
 *   - `seq \in Seq(TDS)` ~> `TRUE`
 *   - `set \in SUBSET TDS` ~> `TRUE`
 *   - `fun \in [TDS1 -> TDS2]` ~> `TRUE`
 *   - `fun \in [Dom -> TDS]` ~> `DOMAIN fun = Dom`
 *   - `tup \in TDS1 \X ... \X TDSn` ~> `TRUE`
 *   - `rec \in [name_1: TDS1, ..., name_n: TDSn]` ~> `TRUE`
 *
 * @author
 *   Thomas Pani
 */
class SetMembershipSimplifier(tracker: TransformationTracker) extends AbstractTransformer(tracker) {
  private val boolTag = Typed(BoolT1)
  private val intTag = Typed(IntT1)
  private def trueVal: ValEx = ValEx(TlaBool(true))(boolTag)

  override val partialTransformers = List(transformMembership)

  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  /**
   * Returns true iff the passed TLA+ expression is a type-defining set. Type-defining sets contain all of the values of
   * their respective element type.
   *
   * The type-defining sets are inductively defined as
   *   - the predefined sets BOOLEAN, Int, Real, STRING,
   *   - sets of sequences over type-defining sets, e.g., Seq(BOOLEAN), Seq(Int), Seq(Seq(Int)), Seq(SUBSET Int), ...
   *   - power sets of type-defining sets, e.g., SUBSET BOOLEAN, SUBSET Int, SUBSET Seq(Int), ...
   *   - sets of functions over type-defining sets, e.g., [Int -> BOOLEAN], ...
   *   - the cartesian product TDS1 \X ...\X TDSn of type-defining sets, e.g., BOOLEAN \X Int, ...
   *   - sets of records over type-defining field types, e.g., [type: STRING, val: Int], ...
   *
   * In particular, `Nat` is not type-defining, nor are sequence sets / power sets thereof, since `i \in Nat` does not
   * hold for all `IntT1`-typed `i`.
   */
  private def isTypeDefining: Function[TlaEx, Boolean] = {
    // base case: BOOLEAN, Int, Real, STRING
    case ValEx(TlaBoolSet) | ValEx(TlaIntSet) | ValEx(TlaRealSet) | ValEx(TlaStrSet) => true

    // inductive cases:
    // 1. Seq(s) for a type-defining set `s`
    case OperEx(TlaSetOper.seqSet, set) => isTypeDefining(set)
    // 2. SUBSET s for a type-defining set `s`
    case OperEx(TlaSetOper.powerset, set) => isTypeDefining(set)
    // 3. [s1 -> s2] for type-defining sets `s1` and `s2`
    case OperEx(TlaSetOper.funSet, set1, set2) => isTypeDefining(set1) && isTypeDefining(set2)
    // 4. s1 \X ... \X sn for type-defining sets `s1` to `sn`
    case OperEx(TlaSetOper.times, args @ _*) => args.forall(isTypeDefining)
    // 5. [name_1: s1, ..., name_n: sn] for type-defining sets `s1` to `sn`
    case OperEx(TlaSetOper.recSet, namesAndSets @ _*) =>
      val (_, sets) = TlaOper.deinterleave(namesAndSets)
      sets.forall(isTypeDefining)

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
    case ex @ OperEx(TlaSetOper.in, name, set) =>
      set match {
        // x \in TDS  ~>  TRUE
        case set if isTypeDefining(set) => trueVal

        // n \in Nat  ~>  x >= 0
        case ValEx(TlaNatSet) => OperEx(TlaArithOper.ge, name, ValEx(TlaInt(0))(intTag))(boolTag)

        // fun \in [Dom -> TDS]  ~>  DOMAIN fun = Dom    (fun \in [TDS1 -> TDS2] is handled above)
        case OperEx(TlaSetOper.funSet, domain, set2) if isTypeDefining(set2) =>
          OperEx(TlaOper.eq, OperEx(TlaFunOper.domain, name)(domain.typeTag), domain)(boolTag)

        // otherwise, return `ex` unchanged
        case _ => ex
      }
    // return non-set membership expressions unchanged
    case ex => ex
  }
}

object SetMembershipSimplifier {
  def apply(tracker: TransformationTracker): SetMembershipSimplifier = new SetMembershipSimplifier(tracker)
}
