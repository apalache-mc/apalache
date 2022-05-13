package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.BuilderUtil.markAsBound
import at.forsyte.apalache.tla.typecomp.subbuilder._
import scalaz.Scalaz._

/**
 * Builder for TLA+ (TNT) IR expressions.
 *
 * The following guarantees hold for any IR tree successfully generated exclusively via ScopedBuilder methods:
 *   - Typed-ness: All subexpressions will have a Typed(_) tag
 *   - Type correctness:
 *     - All literal expressions will have the correct type, as determined by their value ( 1: Int, "a" : Str, etc.)
 *     - For each operator application expression OperEx(oper, args:_*)(Typed(resultType)), the following holds:
 *       - oper(args:_*) corresponds to some TNT operator with a signature (T1,...,Tn) => T
 *       - There exists a substitution s, such that: s(T1) = typeof(args[1]), ..., s(Tn) = typeof(args[n]) and s(T) =
 *         resultType Example: For e@OperEx(TlaSetOper.union, 1..4, {5}) the subexpressions 1..4, {5} and e will all
 *         have types Set(Int), since TlaSetOper.union corresponds to `\`union: (Set(t), Set(t)) => Set(t), and the
 *         substitution required is t -> Int
 *   - Scope correctness: For each variable that appears as free in the IR tree, all instances of that variable will
 *     have the same type. For each sub-tree rooted at an operator, which introduces a bound variable, all instances of
 *     the bound variable will have the same type within the sub-tree. Example: Given \A x \in S: x, if the first x and
 *     S hold the types Int and Set(Int) respectively, while the second x is typed as Bool, the type correctness
 *     requirements imposed by the signature of \A : (t, Set(t), Bool) => Bool are satisfied, but the expression would
 *     not be scope-correct, since x would have to be typed as Int within the scope defined by this \A operator. Thus,
 *     such an expression cannot be constructed by the builder.
 *
 * Note that the guarantees are void if `useTrustedEx` is used.
 *
 * @author
 *   Jure Kukovec
 */
class ScopedBuilder
    extends BaseBuilder with BoolBuilder with ArithmeticBuilder with SetBuilder with SeqBuilder with ActionBuilder
    with LiteralAndNameBuilder {

  /*
  To use the builder outside of testing scenarios, where the expressions aren't written from scratch,
  it is necessary to be able to mark certain expressions as "trusted", e.g. when transforming and recombining invariants,
  or parts of Init/Next.
  While `build` is safe as a unidirectional implicit conversion from TBuilderInstruction to TLaEx,
  the inverse, `useTrustedEx`, needs to be explicit, to stress the fact that it should be used rarely,
  typically at most once per transformation, on the initial input.
   */
  /**
   * Creates a `TBuilderInstruction` from a precomputed `TlaEx`.
   *
   * Should be used sparingly, and only for expressions that have already passed static analysis.
   *
   * Voids correctness guarantees.
   */
  def useTrustedEx(ex: TlaEx): TBuilderInstruction = ex.point[TBuilderInternalState]

  /** x' = y */
  def primeEq(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = eql(prime(x), y)

  type TypedParam = (OperParam, TlaType1)

  /** Parameters to TLA operators can be typed as OperT1 exactly at the top-level, and only if arity > 0 */
  private def isAcceptableParamType(canContainOper: Boolean): TlaType1 => Boolean = {
    case FunT1(arg, res)         => isAcceptableParamType(false)(arg) && isAcceptableParamType(false)(res)
    case SetT1(elem)             => isAcceptableParamType(false)(elem)
    case SeqT1(elem)             => isAcceptableParamType(false)(elem)
    case TupT1(elems @ _*)       => elems.forall(isAcceptableParamType(false))
    case SparseTupT1(fieldTypes) => fieldTypes.values.forall(isAcceptableParamType(false))
    case RecT1(fieldTypes)       => fieldTypes.values.forall(isAcceptableParamType(false))
    case OperT1(args, res) =>
      if (canContainOper)
        args.nonEmpty &&
        args.forall(isAcceptableParamType(false)) &&
        isAcceptableParamType(false)(res)
      else false
    case RowT1(fieldTypes, _) => fieldTypes.values.forall(isAcceptableParamType(false))
    case RecRowT1(row)        => isAcceptableParamType(false)(row)
    case VariantT1(row)       => isAcceptableParamType(false)(row)
    case _                    => true
  }

  private def validateParamType(tp: TypedParam): Unit = {
    val (OperParam(name, arity), tt) = tp
    if (!isAcceptableParamType(canContainOper = arity > 0)(tt))
      throw new TBuilderTypeException(
          s"Parameter $name type $tt and arity $arity are inconsistent. Parameters have operator types iff their arity is positive."
      )
  }

  /**
   * Operator parameter with type information. Checks that parameters have permissible types.
   */
  def param(name: String, tt: TlaType1, arity: Int = 0): TypedParam = {
    val ret = (OperParam(name, arity), tt)
    validateParamType(ret)
    ret
  }

  /** opName(params[1],...,params[n]) == body */
  def decl(opName: String, body: TBuilderInstruction, params: TypedParam*): TBuilderOperDeclInstruction = {
    params.foreach(validateParamType)
    for {
      bodyEx <- body
      // Check param types against their use in body, then mark as bound
      _ <- params.foldLeft(().point[TBuilderInternalState]) { case (cmp, (OperParam(pName, _), tt)) =>
        for {
          _ <- cmp
          pNameEx <- name(pName, tt) // throws scopeException if param name clashes with param use in body
          _ <- markAsBound(pNameEx)
        } yield ()
      }
    } yield TlaOperDecl(opName, params.map(_._1).toList, bodyEx)(
        Typed(
            OperT1(params.map { _._2 }, bodyEx.typeTag.asTlaType1())
        )
    )
  }

  /** Attempt to infer the parameter types from the scope. Fails if a parameter name is not in scope. */
  def declWithInferredParameterTypes(
      opName: String,
      body: TBuilderInstruction,
      untypedParams: OperParam*): TBuilderInternalState[TlaOperDecl] = for {
    bodyEx <- body
    paramTs <- untypedParams.foldLeft(Seq.empty[TlaType1].point[TBuilderInternalState]) {
      case (cmp, OperParam(pName, _)) =>
        for {
          partialTs <- cmp
          pNameEx <- nameWithInferredType(pName) // throws scopeException if param type can't be inferred
          _ <- markAsBound(pNameEx)
        } yield partialTs :+ pNameEx.typeTag.asTlaType1()
    }
  } yield {
    untypedParams.zip(paramTs).foreach(validateParamType)
    TlaOperDecl(opName, untypedParams.toList, bodyEx)(
        Typed(
            OperT1(paramTs, bodyEx.typeTag.asTlaType1())
        )
    )
  }
}
