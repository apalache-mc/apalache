package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.BuilderUtil.{getAllBound, getAllUsed, markAsBound}
import at.forsyte.apalache.tla.typecomp.subbuilder._
import scalaz.Scalaz._

/**
 * Builder for TLA+ (TNT) IR expressions.
 *
 * The following guarantees hold for any IR tree successfully generated exclusively via ScopedBuilder methods:
 *   - Typed-ness: All subexpressions will have a `Typed(_)` tag
 *   - Type correctness:
 *     - All literal expressions will have the correct type, as determined by their value ( `1: Int`, `"a" : Str`, etc.)
 *     - For each operator application expression `OperEx(oper, args:_*)(Typed(resultType))`, the following holds:
 *       - `oper(args:_*)` corresponds to some TNT operator with a signature `(T1,...,Tn) => T`
 *       - There exists some substitution `s`, such that: `s(T1) = typeof(args[1]), ..., s(Tn) = typeof(args[n])` and
 *         `s(T) = resultType`. Example: For `e @ OperEx(TlaSetOper.union, 1..4, {5})` the subexpressions `1..4, {5}`
 *         and `e` will all have types `Set(Int)`, since
 *         [[at.forsyte.apalache.tla.lir.oper.TlaSetOper.union TlaSetOper.union]] corresponds to `\union`, which has the
 *         signature `(Set(t), Set(t)) => Set(t)`, and the substitution required is `t -> Int`.
 *   - Scope correctness: For each variable that appears as free in the IR tree, all instances of that variable will
 *     have the same type. For each sub-tree rooted at an operator, which introduces a bound variable, all instances of
 *     the bound variable will have the same type within the sub-tree. Example: Given `\A x \in S: x`, if the first `x`
 *     and `S` hold the types `Int` and `Set(Int)` respectively, while the second `x` is typed as `Bool`, the type
 *     correctness requirements imposed by the signature of `\A`, `(t, Set(t), Bool) => Bool`, are satisfied, but the
 *     expression would not be scope-correct, since `x` would have to be typed as `Int` within the scope defined by this
 *     `\A` operator. Thus, such an expression cannot be constructed by the builder.
 *
 * These guarantees are void if [[unchecked]] is used.
 *
 * If `strict` mode is enabled, the builder rejects inputs for ApalacheOper methods, which do not adhere to the method
 * requirements ("... must be ..."), even if their types are correct. If `strict` mode is disabled, the builder should
 * allow for the construction of any expression, which may be present in a freshly parsed specification (i.e. before
 * preprocessing).
 *
 * =HOW TO WRITE A NEW METHOD=
 *
 * It is assumed that you are familiar with the package [[typecomp]]. If not, read the [[typecomp]] documentation first.
 *
 * Suppose we want to add a builder method `ScopedBuilder.foo`, for a binary TLA+ operator `Foo(x,y) == ...` which has
 * an internal representation of `foo` (a subclass of [[at.forsyte.apalache.tla.lir.oper.TlaOper TlaOper]]). We need to
 * implement (up to) three leayers, as outlined by [[typecomp]].
 *
 * The Foo example is implemented in `HOWTOFooBuilder` in the tests.
 *
 * ==Determining the type and signature of `Foo`==
 *
 * The first step starts with determining the type of `Foo`. There are two general categories of operators:
 *   1. Operators, for which the type of the operator body depends solely on the types of the parameters
 *   1. Operators, for which the type of the operator body is contextual
 *
 * An example of the first category is `\intersect`; the type of an intersection of two sets equals the types of both of
 * the intersecting sets (which must have the same type). In other words, `\intersect: (Set(t), Set(t)) => Set(t)`. An
 * example of the second is `NotSupportedByModelChecker`; its type can be anything, and is not dependent on the type of
 * the argument (the error message).
 *
 * If the operator belongs to the first category, we need to implement (or extend) a `FooOperSignatures` object in
 * [[signatures]]. Assume, for the purposes of this example, that `Foo` takes two arguments, `x: a` and `y: a -> b`, and
 * returns a value of type `b`, for any pair of types `a` and `b`. This puts `Foo` in the first category.
 *
 * `foo` will have the partial signature
 * {{{
 *   { case Seq(a, FunT1(aa, b)) if a == aa => b }
 * }}}
 * as it requires exactly two arguments, such that the second argument is a function, and the domain-element type of the
 * second argument is equal to the first argument. The return type is equal to the codomain-element type of the second
 * argument. `FooOperSignatures` needs to return a [[SignatureMap]] (via `getMap`), containing an entry for `foo`.
 * [[BuilderUtil.signatureMapEntry signatureMapEntry]] provides a utility method, for constructing such entries from
 * partial functions (the implementation calls [[BuilderUtil.checkForArityException checkForArityException]] and
 * [[BuilderUtil.completePartial completePartial]] in the background, to produce sensible error messages, if
 * `ScopedBuilder.foo` is used with type-incorrect arguments). In our case, using the `signatureMapEntry` helper would
 * look like this:
 * {{{
 *   val fooSig = signatureMapEntry(foo, { case Seq(a, FunT1(aa, b)) if a == aa => b })
 * }}}
 * We then need to make sure that [[TypeComputationFactory]] adds the [[SignatureMap]] from `FooOperSignatures` to its
 * `knownSignatures`.
 *
 * ==Implementing the type-safe builder method==
 *
 * The next step is adding (or extending) a builder in [[unsafe]], `UnsafeFooOperBuilder`. This builder should declare a
 * method `foo(arg1: T1, ..., argN: TN): TlaEx`. The number of arguments depends on the particular operator, and is
 * usually equal to the TLA+ arity of the operator, though this is not always the case. Typically, the argument types
 * are `TlaEx` as well. An exception to this are, for example, operators which take type-hints. Take
 * [[unsafe.UnsafeApalacheInternalBuilder.notSupportedByModelChecker notSupportedByModelChecker]]; it requires a
 * `String` and a [[at.forsyte.apalache.tla.lir.TlaType1 TlaType1]] argument, even though the TLA+ operator
 * `NotSupportedByModelChecker` requires exactly one argument (of type `Str`).
 *
 * In our case, `foo` will need to accept 2 arguments of type [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]], so it will
 * look like
 * {{{
 *   def foo(x: TlaEx, y: TlaEx): TlaEx = ...
 * }}}
 * The implementation depends on whether the operator has an associated signature. If yes, we just need to use
 * [[unsafe.ProtoBuilder.buildBySignatureLookup buildBySignatureLookup]]; All it needs are the operator (`foo`) and a
 * number of [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]] arguments. In our case:
 * {{{
 *   def foo(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(foo, x, y)
 * }}}
 * If we did not have an associated signature, we would have to implement a custom [[TypeComputation]]. See
 * [[unsafe.UnsafeVariantBuilder.variant variant]] or [[unsafe.UnsafeFunBuilder.rec rec]] for examples of this approach.
 *
 * ==Implementing the scope-safe builder method==
 *
 * Finally, we need to add the type-safe, scope-safe method to `FooOperBuilder` in [[subbuilder]]. This builder should
 * declare a method `foo(arg1: TT1, ..., argN: TTN): TBuilderInstruction` and a local instance of `UnsafeFooOperBuilder`
 * (typically named `unsafeBuilder`). The number of arguments should be the same as for the `UnsafeFooOperBuilder.foo`
 * method (we also typically use the same argument names). Each argument that is typed as
 * [[at.forsyte.apalache.tla.lir.TlaEx TlaEx]] in `UnsafeFooOperBuilder.foo` should be typed as [[TBuilderInstruction]]
 * in `FooOperBuilder.foo` (though if an argument in the scope-unsafe method has, for example, a `String` or
 * [[at.forsyte.apalache.tla.lir.TlaType1 TlaType1]] type, it would have that same type in the scope-safe method;
 * strings and [[at.forsyte.apalache.tla.lir.TlaType1 TlaType1]] expressions cannot introduce scope violations). In our
 * case:
 * {{{
 *   def foo(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = ...
 * }}}
 *
 * If the `Foo` operator is not associated with scope modification (e.g. it does not introduce bound variables), all we
 * really need to do is call one of [[BuilderUtil.binaryFromUnsafe binaryFromUnsafe]], or
 * [[BuilderUtil.ternaryFromUnsafe ternaryFromUnsafe]], or [[BuilderUtil.buildSeq buildSeq]] methods. In our case:
 * {{{
 *   def foo(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
 *     binaryFromUnsafe(x, y)(unsafeBuilder.foo)
 * }}}
 * For unary methods, you can just map the unsafe method over a [[TBuilderInstruction]] argument. For methods which deal
 * with bound variables, there are [[BuilderUtil.boundVarIntroductionBinary boundVarIntroductionBinary]],
 * [[BuilderUtil.boundVarIntroductionTernary boundVarIntroductionTernary]], and
 * [[BuilderUtil.boundVarIntroductionVariadic]] (see `subbuilder.BoolBuilder.exists` or
 * [[subbuilder.SetBuilder.map map]].
 *
 * Finally, we just need [[ScopedBuilder]] to extend `FooOperBuilder`, to make the `foo` method available for use.
 *
 * @author
 *   Jure Kukovec
 * @param strict
 *   If true, performs method requirement checks
 */
class ScopedBuilder(val strict: Boolean = true)
    extends BaseBuilder with BoolBuilder with ArithmeticBuilder with SetBuilder with FiniteSetBuilder with SeqBuilder
    with ActionBuilder with FunBuilder with ControlBuilder with TemporalBuilder with ApalacheInternalBuilder
    with ApalacheBuilder with VariantBuilder with LiteralAndNameBuilder {

  /**
   * Creates a `TBuilderInstruction` from a precomputed `TlaEx`. Voids correctness guarantees.
   *
   * Use sparingly, and only for expressions that have already passed static analysis.
   *
   * To use the builder outside of testing scenarios, where the expressions aren't written from scratch, it is necessary
   * to be able to use preexisting expressions, e.g. when transforming and recombining invariants, or parts of
   * Init/Next. While `build` is safe as a unidirectional implicit conversion from `TBuilderInstruction` to TlaEx, the
   * inverse, `unchecked`, needs to be explicit, to stress the fact that it should be used rarely, typically at most
   * once per transformation on the initial input.
   */
  def unchecked(ex: TlaEx): TBuilderInstruction = ex.point[TBuilderInternalState]

  /**
   * @see
   *   [[unchecked]]
   */
  def uncheckedDecl(decl: TlaOperDecl): TBuilderOperDeclInstruction = decl.point[TBuilderInternalState]

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
    case IntT1 | StrT1 | BoolT1 | RealT1 | VarT1(_) | ConstT1(_) => true
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
   * Determines the parameter arity, if the type is an operator type. We distinguish nullary operators from
   * non-operators in this method.
   */
  private def typeAsOperArity(tt: TlaType1): Option[Int] = tt match {
    case OperT1(args, _) => Some(args.size)
    case _               => None
  }

  /**
   * Operator parameter with type information. Checks that parameters have permissible types.
   */
  def param(name: String, tt: TlaType1): TypedParam = {
    val arityOpt = typeAsOperArity(tt)
    // operator parameters may not be nullary operators
    if (arityOpt.contains(0))
      throw new TBuilderTypeException(s"Parameter $name may not have a nullary operator type $tt.")
    val arity = arityOpt.getOrElse(0) // 0 here means not-an-operator
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
      untypedParams: OperParam*): TBuilderOperDeclInstruction = for {
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
   * Creates an expression of the form
   *
   * {{{
   * LET uniqueName(p1,...,pn) == body IN uniqueName
   * }}}
   *
   * Matching the representation of LAMBDAs produced by SANY.
   *
   * NOTE: It is left up to the caller to ensure `uniqueName` is unique.
   *
   * Failure to ensure uniqueness of names can lead to name collisions in case lambdas are nested.
   */
  def lambda(uniqueName: String, body: TBuilderInstruction, params: TypedParam*): TBuilderInstruction = {
    params.foreach(validateParamType)
    for {
      bodyEx <- body
      paramTypes = params.map(_._2)
      operType = OperT1(paramTypes, bodyEx.typeTag.asTlaType1())
      ex <- letIn(name(uniqueName, operType), decl(uniqueName, body, params: _*))
    } yield ex
  }

  /** {{{LET decl(...) = ... IN body}}} */
  def letIn(body: TBuilderInstruction, decl: TBuilderOperDeclInstruction): TBuilderInstruction = for {
    usedBeforeDecl <- getAllUsed // decl name may not appear in decl body
    declEx <- decl
    usedAfterDecl <- getAllUsed
    usedInDecl = usedAfterDecl -- usedBeforeDecl
    bodyEx <- body
    boundAfterBody <- getAllBound // decl may not appear as bound in body
    boundInBody = boundAfterBody -- usedAfterDecl
    declName <- name(declEx.name, declEx.typeTag.asTlaType1()) // puts name in scope w/ type
    _ <- markAsBound(declName)
  } yield {
    if (usedInDecl.union(boundInBody).contains(declEx.name)) {
      val source = if (usedInDecl.contains(declEx.name)) declEx.body else bodyEx
      throw new TBuilderScopeException(s"Declaration name ${declEx.name} is shadowed in $source.")
    } else
      LetInEx(bodyEx, declEx)(bodyEx.typeTag)
  }

  /**
   * {{{LET F_1(a_1^1,...,a_{n_1}^1) == X_1 F_2(a_1^2,...,b_{n_2}^2) == X_2 ... F_N(a_1^N,...,z_{n_N}^N) == X_N IN e}}}
   * is equivalently translated to
   * {{{
   *   LET F_1(a_1^1,...,a_{n_1}^1) == X_1 IN
   *   LET F_2(a_1^2,...,b_{n_2}^2) == X_2 IN
   *   ...
   *   LET F_N(a_1^N,...,z_{n_N}^N) == X_N IN
   *   e
   * }}}
   */
  def letIn(body: TBuilderInstruction, decls: TBuilderOperDeclInstruction*): TBuilderInstruction = {
    require(decls.nonEmpty, "decls must be nonempty.")
    decls.foldRight(body) { case (decl, partial) =>
      letIn(partial, decl)
    }
  }

  /**
   * [f EXCEPT ![a1] = e1, ![a2] = e2 ... ![an] = en]
   *
   * Is equivalent to {{{[[f EXCEPT ![a1] = e1] EXCEPT ![a2] = e2] EXCEPT ... ![an] = en]}}}
   */
  def exceptMany(
      f: TBuilderInstruction,
      args: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction = {
    require(args.nonEmpty, s"args must be nonempty.")
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
  @deprecated
  def exceptDeep(
      f: TBuilderInstruction,
      e: TBuilderInstruction,
      args: TBuilderInstruction*): TBuilderInstruction = {
    require(args.nonEmpty, s"args must be nonempty")

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
  @deprecated
  def exceptGeneral(
      f: TBuilderInstruction,
      args: (TBuilderInstruction, Seq[TBuilderInstruction])*): TBuilderInstruction = {
    // require all depths are the same? Also ensures args.nonEmpty
    require(args.map(_._2.size).toSet.size == 1, s"Expected args to be nonempty and uniformly sized, found $args.")
    args.foldLeft(f) { case (fn, (e, as)) =>
      exceptDeep(fn, e, as: _*)
    }
  }

  /**
   * A name expression referring to the TlaVarDecl
   */
  def varDeclAsNameEx(decl: TlaVarDecl): TBuilderInstruction = {
    name(decl.name, decl.typeTag.asTlaType1())
  }

}
