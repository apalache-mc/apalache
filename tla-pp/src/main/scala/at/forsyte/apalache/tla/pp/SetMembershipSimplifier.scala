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
 *   - `fun \in [Dom -> Nat]` ~> `DOMAIN fun = Dom /\ \A x \in Dom: fun[x] >= 0`
 *   - `tup \in TDS1 \X ... \X TDSn` ~> `TRUE`
 *   - `rec \in [name_1: TDS1, ..., name_n: TDSn]` ~> `TRUE`
 *
 * @param gen
 *   the unique name generator, used for generating bound variable names when simplifying function range constraints
 * @param tracker
 *   the transformation tracker, used for tracking transformations and their effects on the TLA+ expressions
 * @param beforeKeramelizer
 *   whether to perform only a subset of the simplifications that can be safely performed before applying
 *   [[Keramelizer]]
 *
 * @author
 *   Thomas Pani
 */
class SetMembershipSimplifier(
    gen: UniqueNameGenerator,
    tracker: TransformationTracker,
    beforeKeramelizer: Boolean = false)
    extends AbstractTransformer(tracker) {
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

  private def getElemType(e: TlaEx): TlaType1 = {
    e.typeTag match {
      case Typed(SetT1(elemType)) => elemType
      case t                      =>
        throw new MalformedTlaError(s"Expected a set, found: $t", e)
    }
  }

  private def domainEq(fun: TlaEx, domain: TlaEx): TlaEx =
    OperEx(TlaOper.eq, OperEx(TlaFunOper.domain, fun)(domain.typeTag), domain)(boolTag)

  private def natConstraint(elem: TlaEx): TlaEx =
    OperEx(TlaArithOper.ge, elem, ValEx(TlaInt(0))(intTag))(boolTag)

  /**
   * Try to reduce a type-invariant membership to cheaper constraints. This deliberately stays conservative: it only
   * descends into function codomains when the codomain membership itself can be reduced.
   */
  private def simplifyMembership(elem: TlaEx, set: TlaEx): Option[TlaEx] = {
    set match {
      // x \in TDS  ~>  TRUE
      case set if isTypeDefining(set) => Some(trueVal)

      // x \in Nat  ~>  x >= 0
      case ValEx(TlaNatSet) => Some(natConstraint(elem))

      // fun \in [Dom -> TDS]  ~>  DOMAIN fun = Dom
      case OperEx(TlaSetOper.funSet, domain, codomain) if isTypeDefining(codomain) =>
        Some(domainEq(elem, domain))

      // fun \in [Dom -> Range]  ~>  DOMAIN fun = Dom /\ \A x \in Dom: fun[x] \in Range,
      // if the range check can itself be reduced by this simplifier.
      case OperEx(TlaSetOper.funSet, domain, codomain) =>
        val domElemType = getElemType(domain)
        val codomainElemType = getElemType(codomain)
        val domElem = NameEx(gen.newName())(Typed(domElemType))
        val app = OperEx(TlaFunOper.app, elem, domElem)(Typed(codomainElemType))
        simplifyMembership(app, codomain).map { rangeConstraint =>
          OperEx(TlaBoolOper.and, domainEq(elem, domain),
              OperEx(TlaBoolOper.forall, domElem, domain, rangeConstraint)(boolTag))(boolTag)
        }

      case _ => None
    }
  }

  private def isFunctionSetWithReducibleNonTypeDefRange(set: TlaEx): Boolean = set match {
    case OperEx(TlaSetOper.funSet, _, codomain) if !isTypeDefining(codomain) =>
      codomain match {
        case ValEx(TlaNatSet)                         => true
        case nested @ OperEx(TlaSetOper.funSet, _, _) => isFunctionSetWithReducibleNonTypeDefRange(nested)
        case _                                        => false
      }

    case _ => false
  }

  private def simplifyBeforeKeramelizer(elem: TlaEx, set: TlaEx): Option[TlaEx] = set match {
    // Keep the early pass narrow. In particular, do not simplify assignments such as `b' \in BOOLEAN`.
    case OperEx(TlaSetOper.funSet, _, codomain @ OperEx(TlaSetOper.funSet, _, nestedCodomain))
        if isReducibleNonTypeDefRange(nestedCodomain) =>
      simplifyMembership(elem, set)

    case _ => None
  }

  /**
   * Simplifies expressions commonly found in `TypeOK`, assuming they are well-typed.
   *
   * @see
   *   [[SetMembershipSimplifier]] for a full list of supported rewritings.
   */
  private def transformMembership: PartialFunction[TlaEx, TlaEx] = {
    case ex @ OperEx(TlaSetOper.in, name, set) =>
      val simplified =
        if (beforeKeramelizer) {
          simplifyBeforeKeramelizer(name, set)
        } else {
          simplifyMembership(name, set)
        }
      simplified.getOrElse(ex)
    // return non-set membership expressions unchanged
    case ex => ex
  }
}

object SetMembershipSimplifier {
  def apply(gen: UniqueNameGenerator, tracker: TransformationTracker): SetMembershipSimplifier =
    new SetMembershipSimplifier(gen, tracker)

  def beforeKeramelizer(gen: UniqueNameGenerator, tracker: TransformationTracker): SetMembershipSimplifier =
    new SetMembershipSimplifier(gen, tracker, beforeKeramelizer = true)
}
