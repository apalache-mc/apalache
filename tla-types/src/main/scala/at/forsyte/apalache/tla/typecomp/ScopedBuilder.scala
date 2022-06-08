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
 * These guarantees are void if [[useTrustedEx]] is used.
 *
 * @author
 *   Jure Kukovec
 */
class ScopedBuilder
    extends BaseBuilder with BoolBuilder with ArithmeticBuilder with SetBuilder with SeqBuilder with ActionBuilder
    with FunBuilder with ControlBuilder with LiteralAndNameBuilder {

  /**
   * Creates a `TBuilderInstruction` from a precomputed `TlaEx`. Voids correctness guarantees.
   *
   * Use sparingly, and only for expressions that have already passed static analysis.
   *
   * To use the builder outside of testing scenarios, where the expressions aren't written from scratch, it is necessary
   * to be able to mark certain expressions as "trusted", e.g. when transforming and recombining invariants, or parts of
   * Init/Next. While `build` is safe as a unidirectional implicit conversion from `TBuilderInstruction` to TlaEx, the
   * inverse, `useTrustedEx`, needs to be explicit, to stress the fact that it should be used rarely, typically at most
   * once per transformation on the initial input.
   */
  def useTrustedEx(ex: TlaEx): TBuilderInstruction = ex.point[TBuilderInternalState]

  ////////////////////
  // HYBRID METHODS //
  ////////////////////

  /** x' = y */
  def primeEq(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = eql(prime(x), y)

  type TypedParam = (OperParam, TlaType1)

  /**
   * Evaluates whether a parameter type satisfies the type restrictions on operator parameters in TLA+.
   *
   * Parameters of TLA+ operators must:
   *   - have a non-operator type, unless they are (syntactically) marked higher-order (HO)
   *   - have a top-level operator type (OperT1) if they are marked HO
   *   - not contain `OperT1` in the type's syntax-tree in either case, except possibly at the root (if HO). In
   *     particular, a parameter to a HO operator with an `OperT1` type may not be HO itself.
   */
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

  /**
   * Throws if parameters don't satisfy [[isAcceptableParamType]]. Permits operator types iff the parameter arity is
   * positive.
   */
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

  /** Infer parameter types from the scope. Fails if a parameter name is not in scope. */
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

  /**
   * [f EXCEPT ![a1] = e1, ![a2] = e2 ... ![an] = en]
   *
   * Is equivalent to {{{[[f EXCEPT ![a1] = e1] EXCEPT ![a2] = e2] EXCEPT ... ![an] = en]}}}
   */
  def exceptMany(
      f: TBuilderInstruction,
      args: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction = {
    require(args.nonEmpty)
    args.foldLeft(f) { case (fn, (ai, ei)) =>
      except(fn, ai, ei)
    }
  }

  /**
   * [f EXCEPT ![a1][a2][...][an] = e]
   *
   * Is equivalent to {{{[f EXCEPT ![a1] = [f[a1] EXCEPT ![a2] = [ ... EXCEPT ![an] = e]]]}}}
   *
   * The use of this constructor is discouraged in non-legacy code, as deep-EXCEPT syntax impedes readability, since the
   * types of intermediate objects are obfuscated.
   */
  def exceptDeep(
      f: TBuilderInstruction,
      e: TBuilderInstruction,
      args: TBuilderInstruction*): TBuilderInstruction = {
    require(args.nonEmpty)

    args match {
      case Seq(head) => except(f, head, e)
      case head +: tail =>
        except(
            f,
            head,
            exceptDeep(app(f, head), e, tail: _*),
        )
    }
  }

  /**
   * [f EXCEPT ![a1][a2][...][an] = ea, ![b1][b2][...][bn] = eb, ..., ![z1][z2][...][zn] = ez]
   *
   * @param args
   *   Pairs of the shape (ei, Seq(i1, ..., in))
   *
   * The use of this constructor is discouraged in non-legacy code, as deep-EXCEPT syntax impedes readability, since the
   * types of intermediate objects are obfuscated.
   */
  def exceptGeneral(
      f: TBuilderInstruction,
      args: (TBuilderInstruction, Seq[TBuilderInstruction])*): TBuilderInstruction = {
    // require all depths are the same? Also ensures args.nonEmpty
    require(args.map(_._2.size).toSet.size == 1)
    args.foldLeft(f) { case (fn, (e, as)) =>
      exceptDeep(fn, e, as: _*)
    }
  }

  /**
   * [x1 \in S1, ..., xn \in Sn |-> e]
   *
   * Is equivalent to {{{[<<x1,...,xn>> \in S1 \X ... \X Sn |-> e]}}}
   */
  def funDef(e: TBuilderInstruction, args: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction = {
    require(args.nonEmpty)
    val (elems, sets) = args.unzip
    funDef(e, tuple(elems: _*), times(sets: _*))
  }

  /**
   * A name expression referring to the TlaVarDecl
   */
  def varDeclAsNameEx(decl: TlaVarDecl): TBuilderInstruction = {
    name(decl.name, decl.typeTag.asTlaType1())
  }

}
