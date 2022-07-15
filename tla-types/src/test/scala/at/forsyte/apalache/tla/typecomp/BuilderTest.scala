package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalatest.{AppendedClues, BeforeAndAfter}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers
import shapeless._

import scala.collection.immutable.SortedMap

// /////////////////////////////
// // HOW TO WRITE A NEW TEST //
// /////////////////////////////
//
// Suppose we want to add a test for TLA+ operator (binary, in this example), `Foo(x,y) == ...`
// which has an internal representation of `foo` and is built by the `builder.foo` method.
// Assume, for the purposes of this example, that Foo takes two arguments - x: a and y: a -> b -
// and returns a value of type b, for any pair of types a and b.
//
// We add a test("foo") to TestOperCategoryBuilder, where OperCategory is the class of operators foo belongs to
// (TlaSetOper, ApalacheOper, etc.).
// Our goal is to use `BuilderTest.checkRun` to test `builder.foo` on inputs of varying types. To do this, we
// need to determine the following:
//
// 1) The number of arguments to `builder.foo` and their types.
//    In our example, `builder.foo` takes two TBuilderInstruction arguments.
//    Typically, we introduce a type alias, so in our case
//    type T = (TBuilderInstruction, TBuilderInstruction)
//
// 2) The number and types of the automatically generated parameters
//    In our example, `Foo` has a polymorphic signature, that takes two type parameters (a, b).
//    Typically, we introduce a type alias, so in our case
//    type TParam = (TlaType1, TlaType1)
//
// 3) A description of a test run, for a fixed instance of parameters
//    checkRun accepts two arguments: a generator (discussed later) and a `run`, which is a
//    function from TParam to Bool. A `run` should test the builder method (e.g. `builder.foo`) for
//    parameterized correctness (tested against all parameters produced by the generator),
//    and should return true every time if the method is correctly implemented.
//    You _can_ write a custom run, but the recommended way is to use one of the pre-written templates, i.e.
//    runUnary, runBinary, runTernary, runVariadic, or runVariadicWithDistinguishedFirst (depending on the arity of
//    the builder method).
//
// Assume we want to use the `runBinary` template to test our `builder.foo`. Regardless of arity, each template
// takes four arguments:
// a) The method. In our case `builder.foo`. runBinary requires a binary method, other templates require methods
//    of their corresponding arities.
// b) A well-typed argument constructor `mkWellTyped`. It should have the type TParam => T, i.e., given
//    type parameters, it should construct a pair of arguments (x,y), such that `build(builder.foo(x,y)` succeeds.
//    In our case:
//    def mkWellTyped(tparam: TParam): T = {
//      val (a, b) = tparam
//      (
//       builder.name("x", a),
//       builder.name("y", FunT1(a, b))
//      )
//    }
//    since the 1st argument must have a a type, and the 2nd a a -> b type.
// c) A constructor of ill-typed arguments `mkIllTyped`. It should have the type TParam => Seq[T], i.e., given
//    type parameters, it should construct a sequence of pairs of arguments (x,y), such that
//    `build(builder.foo(x,y)` produces a TBuilderTypeException for each pair.
//    In our case:
//    def mkIllTyped(tparam: TParam): Seq[T] = {
//      val (a, b) = tparam
//      Seq(
//          (
//              builder.name("x", InvalidTypeMethods.differentFrom(a)),
//              builder.name("y", FunT1(a, b)),
//          ),
//          (
//              builder.name("x", a),
//              builder.name("y", InvalidTypeMethods.notApplicative),
//          ),
//          (
//              builder.name("x", a),
//              builder.name("y", FunT1(InvalidTypeMethods.differentFrom(a), b)),
//          ),
//      )
//    }
//    Since there are three ways of violating the type constraints:
//      - If x has the type c and y has the type a -> b, where c /= a
//      - If y doesn't have a function type at all
//      - If x has the type a and y has the type c -> b, where c /= a
//
//    Note that the following is _not_ ill-typed:
//    (
//        builder.name("x", a),
//        builder.name("y", FunT1(a, InvalidTypeMethods.differentFrom(b))),
//    ),
//    Since b isn't checked against any other argument, unlike a, if we swap b with some c
//    we get arguments with types a and a -> c, which is still valid w.r.t. the signature of foo, and would
//    return some value of type c.
//
//    Note that some operators, for example those that take one argument of any type, have no ill-typed
//    inputs. In those cases,
//    def mkIllTyped(@unused tparam: TParam): Seq[T] = Seq.empty
//
// d) A validator test `resultIsExpected`. It should have the type TParam => ResultT => Boolean, i.e.,
//    if `method` produces a value of type TBuilderInternalState[ResultT] (recall, TBuilderInstruction is an alias
//    for TBuilderInternalState[TlaEx]), then resultIsExpected is a predicate over values of type ResultT (parameterized
//    by TParam) that should return true iff the value produced by `method` meets expectations.
//    In the vast majority of cases (excluding e.g. declaration constructors), ResultT == TlaEx.
//    You can write your own, but the standard way is to use `expectEqTyped`, which tests whether the builder
//    constructs an OperEx expression, with the correct operator, arguments, and type tag.
//
// To use `expectEqTyped`, four things are needed:
// i) The expected operator `op`. In our case, `foo`.
// ii) A parametric constructor for the expected arguments. You should always use `mkWellTyped`.
// iii) A transformer to turn a tuple of arguments into a sequence of arguments `toSeq`. This is required, due to the
//      underlying shapeless framework, which allows us to generalize tests over all method arities.
//      In the vast majority of cases, you can use the method in ToSeq, corresponding to the method arity.
//      In our case, `ToSeq.binary`.
// iv) A predictor of the type of the return value `resType`, parameterized by the type parameters.
//     In our case { case (_, b) => b }
//
// In summary, the test for builder.foo is:
// def resultIsExpected = expectEqTyped[TParam, T](
//   foo,
//   mkWellTyped,
//   ToSeq.binary,
//   { case (_, b) => b },
// )
//
// Lastly, we need to define a generator for TParam. In most cases, you can use one of the generators defined in
// Generators. In our case Generators.doubleTypeGen for (TlaType1, TlaType1).
//
// The Foo example is implemented in HOWTOTestFooBuilder

/**
 * BuilderTest implements a framework for PB testing various Builder methods.
 *
 * Since builder methods have many different arities no useful Scala-native supertype to represent the type of a builder
 * method in full generality. To this end, we use shapeless' HList (H for heterogeneous) as a representation of any
 * builder method's argument types. For example:
 *   - plus has the signature (TBuilderInstruction,TBuilderInstruction) => TBuilderInstruction, represented by
 *     TBuilderInstruction :: TBuilderInstruction :: HNil <: HList
 *   - union has the signature (TBuilderInstruction) => TBuilderInstruction, and is represented by the type
 *     TBuilderInstruction :: HNil <: HList
 *   - map has the signature (TBuilderInstruction, TBuilderInstruction*) => TBuilderInstruction, represented by
 *     TBuilderInstruction :: Seq[TBuilderInstruction] :: HNil <: HList
 *
 * The central method, with various convenience extensions, is runPBT, which performs the following testing tasks:
 *   - Tests whether a TBuilderInstruction, which is supposed to construct a well-typed operator expression actually
 *     does
 *   - Tests whether all of the inputs which would have produced an ill-typed expression actually cause `build` to fail
 */
@RunWith(classOf[JUnitRunner])
trait BuilderTest extends AnyFunSuite with BeforeAndAfter with Checkers with AppendedClues with Matchers {
  var builder = new ScopedBuilder
  var cmpFactory = new TypeComputationFactory

  before {
    builder = new ScopedBuilder
    cmpFactory = new TypeComputationFactory
  }

  type DeclParamT = (TlaType1, Seq[TlaType1])

  /** Contains definitions of parameterization generators */
  object Generators {

    val unitGen: Gen[Unit] = Gen.const(())

    def minIntGen(min: Int) = Gen.choose(min, min + 10)

    val positiveIntGen: Gen[Int] = minIntGen(1)
    val nonnegativeIntGen: Gen[Int] = minIntGen(0)

    protected val tt1gen: TlaType1Gen = new TlaType1Gen {}

    val singleTypeGen: Gen[TlaType1] = tt1gen.genType1
    val doubleTypeGen: Gen[(TlaType1, TlaType1)] = Gen.zip(singleTypeGen, singleTypeGen)

    val parameterTypeGen: Gen[TlaType1] = for {
      t <- tt1gen.genPrimitive
      n <- nonnegativeIntGen
      ts <- Gen.listOfN(n, tt1gen.genPrimitive)
    } yield n match {
      case 0          => t
      case m if m > 0 => OperT1(ts, t)
      case _          =>
        // impossible, since 0 <= n <= 5, but the compiler doesn't know and complains
        throw new IllegalStateException("Expected n to be nonnegative.")
    }

    val doubleParameterTypeGen: Gen[(TlaType1, TlaType1)] = Gen.zip(parameterTypeGen, parameterTypeGen)

    val declTypesGen: Gen[DeclParamT] = for {
      t <- singleTypeGen
      n <- nonnegativeIntGen
      ts <- Gen.listOfN(n, parameterTypeGen)
    } yield (t, ts)

    val typeAndDeclGen: Gen[(TlaType1, DeclParamT)] = Gen.zip(singleTypeGen, declTypesGen)
    val typeAndListOfDeclsGen: Gen[(TlaType1, Seq[DeclParamT])] = Gen.zip(
        singleTypeGen,
        positiveIntGen.flatMap(Gen.listOfN(_, declTypesGen)),
    )

    def seqOfTypesGenMinLenGen(min: Int) = minIntGen(min).flatMap(Gen.listOfN(_, singleTypeGen))

    val seqOfTypesGen: Gen[Seq[TlaType1]] = seqOfTypesGenMinLenGen(0)
    val nonemptySeqOfTypesGen: Gen[Seq[TlaType1]] = seqOfTypesGenMinLenGen(1)

    val typeAndSeqGen: Gen[(TlaType1, Seq[TlaType1])] = Gen.zip(singleTypeGen, seqOfTypesGen)
    val typeAndNonemptySeqGen: Gen[(TlaType1, Seq[TlaType1])] = Gen.zip(singleTypeGen, nonemptySeqOfTypesGen)

    // unsafe for non-applicative
    private def argGen(appT: TlaType1): Gen[TBuilderInstruction] = (appT: @unchecked) match {
      case FunT1(a, _) => Gen.const(builder.name("x", a))
      case TupT1(args @ _*) => // assume nonempty
        Gen.choose[BigInt](1, args.size).map(builder.int)
      case RecT1(flds) => // assume nonempty
        Gen.oneOf(flds.keys).map(builder.str)
      case _: SeqT1 => Gen.const(builder.name("x", IntT1))
    }

    val applicativeGen: Gen[TlaType1] = Gen.oneOf(tt1gen.genFun, tt1gen.genRec, tt1gen.genSeq, tt1gen.genTup)

    val applicativeAndArgGen: Gen[(TlaType1, TBuilderInstruction)] = for {
      appT <- applicativeGen
      arg <- argGen(appT)
    } yield (appT, arg)

    private var ctr: Int = 0
    // unsafe for non-applicative
    def argAndCdmTypeGen(appT: TlaType1): Gen[(TBuilderInstruction, TlaType1)] = {
      ctr += 1
      (appT: @unchecked) match {
        case FunT1(a, b) => Gen.const((builder.name(s"x$ctr", a), b))
        case TupT1(args @ _*) => // assume nonempty
          Gen.choose[Int](1, args.size).map(i => (builder.int(i), args(i - 1)))
        case RecT1(flds) => // assume nonempty
          Gen.oneOf(flds.keys).map(k => (builder.str(k), flds(k)))
        case SeqT1(t) => Gen.const((builder.name(s"x$ctr", IntT1), t))
      }
    }

    val applicativeAndSeqArgCdmGen: Gen[(TlaType1, Seq[(TBuilderInstruction, TlaType1)])] = for {
      t <- applicativeGen
      n <- positiveIntGen
      seq <- Gen.listOfN(n, argAndCdmTypeGen(t))
    } yield (t, seq)

    val positiveIntAndTypeGen: Gen[(Int, TlaType1)] = Gen.zip(positiveIntGen, singleTypeGen)
    val nonnegativeIntAndTypeGen: Gen[(Int, TlaType1)] = Gen.zip(nonnegativeIntGen, singleTypeGen)

    val strGen: Gen[String] = Gen.alphaStr

    val strAndTypeGen: Gen[(String, TlaType1)] = Gen.zip(strGen, singleTypeGen)

    val variantGen: Gen[VariantT1] = for {
      n <- Gen.choose(1, 5)
      flds <- Gen.listOfN(n, Gen.zip(strGen, singleTypeGen))
    } yield VariantT1(RowT1(SortedMap(flds: _*), None))

    def variantGenWithMandatoryEntry(mandatoryEntry: (String, TlaType1)): Gen[VariantT1] = variantGen.map { variantT =>
      VariantT1(RowT1(variantT.row.fieldTypes + mandatoryEntry, None))
    }

    def variantGenWithMandatoryField(mandatoryField: String): Gen[VariantT1] =
      singleTypeGen.flatMap { fldT =>
        variantGenWithMandatoryEntry(mandatoryField -> fldT)
      }

    val tagAndVariantGen: Gen[(String, VariantT1)] = for {
      tagName <- strGen
      variantT <- variantGenWithMandatoryField(tagName)
    } yield (tagName, variantT)

    val tagValVariantGen: Gen[(String, TlaType1, VariantT1)] = for {
      tagName <- strGen
      valT <- singleTypeGen
      variantT <- variantGenWithMandatoryEntry(tagName -> valT)
    } yield (tagName, valT, variantT)

  }

  // Useful methods for defining mkIllTypedArgs
  object InvalidTypeMethods {
    def notSet: TlaType1 = IntT1
    def notSeq: TlaType1 = IntT1
    def notTup: TlaType1 = IntT1
    def notOper: TlaType1 = IntT1
    def notBool: TlaType1 = differentFrom(BoolT1)
    def notInt: TlaType1 = differentFrom(IntT1)
    def notApplicative: TlaType1 = IntT1
    def notVariant: TlaType1 = IntT1
    def differentFrom(tt: TlaType1): TlaType1 = if (tt == IntT1) StrT1 else IntT1
  }

  /** Defines a collection of standard conversion methods, to be used as `toSeq` in `expectEqTyped` */
  object ToSeq {
    def unary[T](implicit convert: T => TBuilderInstruction): T => Seq[TBuilderResult] = { v => Seq(convert(v)) }
    def binary[T1, T2](
        implicit convert1: T1 => TBuilderInstruction,
        convert2: T2 => TBuilderInstruction): ((T1, T2)) => Seq[TBuilderResult] = { case (a, b) =>
      Seq(convert1(a), convert2(b))
    }
    def ternary[T1, T2, T3](
        implicit convert1: T1 => TBuilderInstruction,
        convert2: T2 => TBuilderInstruction,
        convert3: T3 => TBuilderInstruction): ((T1, T2, T3)) => Seq[TBuilderResult] = { case (a, b, c) =>
      Seq(convert1(a), convert2(b), convert3(c))
    }
    def variadic[T](implicit convert: T => TBuilderInstruction): Seq[T] => Seq[TBuilderResult] = { seq =>
      liftBuildToSeq(seq.map(convert))
    }
    def variadicPairs[T1, T2](
        implicit convert1: T1 => TBuilderInstruction,
        convert2: T2 => TBuilderInstruction): Seq[(T1, T2)] => Seq[TBuilderResult] =
      _.flatMap(binary[T1, T2](convert1, convert2))
    def variadicWithDistinguishedFirst[T1, T2](
        implicit convert1: T1 => TBuilderInstruction,
        convert2: T2 => TBuilderInstruction): ((T1, Seq[T2])) => Seq[TBuilderResult] = { case (a, seq) =>
      build(convert1(a)) +: variadic[T2](convert2)(seq)
    }
    def variadicPairsWithDistinguishedFirst[T1, T2, T3](
        implicit convert1: T1 => TBuilderInstruction,
        convert2: T2 => TBuilderInstruction,
        convert3: T3 => TBuilderInstruction): ((T1, Seq[(T2, T3)])) => Seq[TBuilderResult] = { case (a, seq) =>
      build(convert1(a)) +: variadicPairs[T2, T3](convert2, convert3)(seq)
    }
  }
  implicit val strToBuilderI: String => TBuilderInstruction = builder.str
  implicit val intToBuilderI: Int => TBuilderInstruction = { i => builder.int(i) } // coerces implcit cast Int -> BigInt

  /** Convenience method, for constructing resultIsExpected as an test of eqTyped */
  def expectEqTyped[TypeParameterization, T](
      op: TlaOper,
      mkWellTyped: TypeParameterization => T,
      toSeq: T => Seq[TBuilderResult],
      resType: TypeParameterization => TlaType1): TypeParameterization => TBuilderResult => Boolean = {
    tparam =>
      { resEx =>
        resEx.eqTyped(
            OperEx(
                op,
                toSeq(mkWellTyped(tparam)): _*
            )(Typed(resType(tparam)))
        )
      }
  }

  /**
   * Central testing method. Recommended to use the convenience methods testUnary, testBinary, etc. whenever possible.
   *
   * @param methodH
   *   A builder method lifted to HList. For example, builder.binaryMethod(_,_) can be tested as { case a :: b :: HNil
   *   \=> builder.binaryMethod(_,_) }
   * @param mkWellTypedArgs
   *   A method that, given a TypeParameterization, produces list of arguments to methodH, which are expected to
   *   generate a TBuilderInstruction which successfully builds
   * @param mkIllTypedArgs
   *   A method that, given a TypeParameterization, produces collection of lists of arguments to methodH, which are all
   *   expected to generate TBuilderInstructions which fail to build
   * @param resultIsExpected
   *   Judgement method, which asserts whether the expression produced by building the instruction generated by
   *   methodH(mkWellTypedArgs(_)) satisfies expectations
   * @param tparam
   *   Concrete instance of type parameter(s) under test
   * @tparam H
   *   Particular variant of HList, based on the method being tested. For example, testing a binary method will have H
   *   equal to TBuilderInstruction :: TBuilderInstruction :: HNil, while testing a variadic method will have H equal to
   *   Seq[TBuilderInstruction] :: HNil
   * @tparam TypeParameterization
   *   Degree of polymorphism. Unit if testing non-polymorphic methods, TlaType1, if testing a method with one type
   *   parameter, Seq[TlaType1] if testing a method with many type parameters, etc.
   */
  def runPBT[H <: HList, TypeParameterization, BuilderResultT](
      methodH: PartialFunction[H, TBuilderInternalState[BuilderResultT]],
      mkWellTypedArgs: TypeParameterization => H,
      mkIllTypedArgs: TypeParameterization => Seq[H], // some operators cannot be passed an invalid arg
      resultIsExpected: TypeParameterization => BuilderResultT => Boolean,
    )(tparam: TypeParameterization): Boolean = {
    val wellTypedH = mkWellTypedArgs(tparam)
    val illTypedIs = mkIllTypedArgs(tparam).map(methodH)
    val resEx = build(methodH(wellTypedH))

    val isAsExpected = resultIsExpected(tparam)(resEx)

    isAsExpected shouldBe true

    illTypedIs.foreach { bi =>
      assertThrows[TBuilderTypeException] {
        build(bi)
      }
    }

    true
  }

  /** test `run` against a generator of TypeParameterization values */
  def checkRun[TypeParameterization](typegen: Gen[TypeParameterization])(run: TypeParameterization => Boolean): Unit = {
    val prop = forAll(typegen) { run }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  /** Invokes tests for a unary builder method. Performs lifting to HList logic for the user. */
  def runUnary[TypeParameterization, ArgumentT1, ResultT](
      method: ArgumentT1 => TBuilderInternalState[ResultT],
      mkWellTypedArg: TypeParameterization => ArgumentT1,
      mkIllTypedArg: TypeParameterization => Seq[ArgumentT1],
      resultIsExpected: TypeParameterization => ResultT => Boolean,
    )(tparam: TypeParameterization): Boolean = {

    type H = ArgumentT1 :: HNil
    def mkWellTypedArgH(tparam: TypeParameterization): H = mkWellTypedArg(tparam) :: HNil
    def mkIllTypedArgH(tparam: TypeParameterization): Seq[H] = mkIllTypedArg(tparam).map { _ :: HNil }
    def methodH: PartialFunction[H, TBuilderInternalState[ResultT]] = { case a :: HNil =>
      method(a)
    }

    runPBT(
        methodH,
        mkWellTypedArgH,
        mkIllTypedArgH,
        resultIsExpected,
    )(tparam)
  }

  /** Invokes tests for a binary builder method. Performs lifting to HList logic for the user. */
  def runBinary[TypeParameterization, ArgumentT1, ArgumentT2, ResultT](
      method: (ArgumentT1, ArgumentT2) => TBuilderInternalState[ResultT],
      mkWellTypedArg: TypeParameterization => (ArgumentT1, ArgumentT2),
      mkIllTypedArg: TypeParameterization => Seq[(ArgumentT1, ArgumentT2)],
      resultIsExpected: TypeParameterization => ResultT => Boolean,
    )(tparam: TypeParameterization): Boolean = {

    type H = ArgumentT1 :: ArgumentT2 :: HNil
    def mkWellTypedArgH(tparam: TypeParameterization): H = {
      val (a, b) = mkWellTypedArg(tparam)
      a :: b :: HNil
    }
    def mkIllTypedArgH(tparam: TypeParameterization): Seq[H] = mkIllTypedArg(tparam).map { case (a, b) =>
      a :: b :: HNil
    }
    def methodH: PartialFunction[H, TBuilderInternalState[ResultT]] = { case a :: b :: HNil =>
      method(a, b)
    }

    runPBT(
        methodH,
        mkWellTypedArgH,
        mkIllTypedArgH,
        resultIsExpected,
    )(tparam)
  }

  /** Invokes tests for a ternary builder method. Performs lifting to HList logic for the user. */
  def runTernary[TypeParameterization, ArgumentT1, ArgumentT2, ArgumentT3, ResultT](
      method: (ArgumentT1, ArgumentT2, ArgumentT3) => TBuilderInternalState[ResultT],
      mkWellTypedArg: TypeParameterization => (ArgumentT1, ArgumentT2, ArgumentT3),
      mkIllTypedArg: TypeParameterization => Seq[(ArgumentT1, ArgumentT2, ArgumentT3)],
      resultIsExpected: TypeParameterization => ResultT => Boolean,
    )(tparam: TypeParameterization): Boolean = {

    type H = ArgumentT1 :: ArgumentT2 :: ArgumentT3 :: HNil
    def mkWellTypedArgH(tparam: TypeParameterization): H = {
      val (a, b, c) = mkWellTypedArg(tparam)
      a :: b :: c :: HNil
    }
    def mkIllTypedArgH(tparam: TypeParameterization): Seq[H] = mkIllTypedArg(tparam).map { case (a, b, c) =>
      a :: b :: c :: HNil
    }
    def methodH: PartialFunction[H, TBuilderInternalState[ResultT]] = { case a :: b :: c :: HNil =>
      method(a, b, c)
    }

    runPBT(
        methodH,
        mkWellTypedArgH,
        mkIllTypedArgH,
        resultIsExpected,
    )(tparam)
  }

  /** Invokes tests for a variadic builder method. Performs lifting to HList logic for the user. */
  def runVariadic[TypeParameterization, ArgumentT, ResultT](
      method: Seq[ArgumentT] => TBuilderInternalState[ResultT],
      mkWellTypedArg: TypeParameterization => Seq[ArgumentT],
      mkIllTypedArg: TypeParameterization => Seq[Seq[ArgumentT]],
      resultIsExpected: TypeParameterization => ResultT => Boolean,
    )(tparam: TypeParameterization): Boolean = {

    type H = Seq[ArgumentT] :: HNil
    def mkWellTypedArgH(tparam: TypeParameterization): H =
      mkWellTypedArg(tparam) :: HNil

    def mkIllTypedArgH(tparam: TypeParameterization): Seq[H] = mkIllTypedArg(tparam).map { _ :: HNil }

    def methodH: PartialFunction[H, TBuilderInternalState[ResultT]] = { case seq :: HNil =>
      method(seq)
    }

    runPBT(
        methodH,
        mkWellTypedArgH,
        mkIllTypedArgH,
        resultIsExpected,
    )(tparam)
  }

  /**
   * Invokes tests for a variadic builder method with a distinguished first argument. Performs lifting to HList logic
   * for the user.
   */
  def runVariadicWithDistinguishedFirst[TypeParameterization, ArgumentT1, SeqArgumentsT, ResultT](
      method: (ArgumentT1, Seq[SeqArgumentsT]) => TBuilderInternalState[ResultT],
      mkWellTypedArg: TypeParameterization => (ArgumentT1, Seq[SeqArgumentsT]),
      mkIllTypedArg: TypeParameterization => Seq[(ArgumentT1, Seq[SeqArgumentsT])],
      resultIsExpected: TypeParameterization => ResultT => Boolean,
    )(tparam: TypeParameterization): Boolean = {

    type H = ArgumentT1 :: Seq[SeqArgumentsT] :: HNil
    def mkWellTypedArgH(tparam: TypeParameterization): H = {
      val (a, seq) = mkWellTypedArg(tparam)
      a :: seq :: HNil
    }

    def mkIllTypedArgH(tparam: TypeParameterization): Seq[H] =
      mkIllTypedArg(tparam).map { case (a, seq) => a :: seq :: HNil }

    def methodH: PartialFunction[H, TBuilderInternalState[ResultT]] = { case a :: seq :: HNil =>
      method(a, seq)
    }

    runPBT(
        methodH,
        mkWellTypedArgH,
        mkIllTypedArgH,
        resultIsExpected,
    )(tparam)
  }

  def assertThrowsBoundVarIntroductionTernary(
      // order: variable, set, expr
      method: (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction): Unit = {
    // test fail on non-name
    assertThrows[IllegalArgumentException] {
      build(
          method(
              builder.str("x"), // got ValEx(TlaStr), expected NameEx
              builder.name("S", SetT1(StrT1)),
              builder.bool(true),
          )
      )
    }

    // test fail on scope error
    assertThrows[TBuilderScopeException] {
      build(
          method(
              builder.name("x", StrT1), // x: Str
              builder.name("S", SetT1(StrT1)),
              builder.eql(builder.name("x", IntT1), builder.name("x", IntT1)), // x: Int
          )
      )
    }

    // test fail on shadowing
    assertThrows[TBuilderScopeException] {
      build(
          // Op(x, {x}, TRUE)
          method(
              builder.name("x", StrT1),
              builder.enumSet(builder.name("x", StrT1)),
              builder.bool(true),
          )
      )
    }

    assertThrows[TBuilderScopeException] {
      build(
          // Op( x, S, \E x \in S: TRUE)
          method(
              builder.name("x", StrT1),
              builder.name("S", SetT1(StrT1)),
              builder.exists(
                  builder.name("x", StrT1),
                  builder.name("S", SetT1(StrT1)),
                  builder.bool(true),
              ),
          )
      )
    }
  }

  def assertThrowsBoundVarIntroductionBinary(
      // order: variable, expr
      method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction): Unit = {
    // test fail on non-name
    assertThrows[IllegalArgumentException] {
      build(
          method(
              builder.str("x"), // got ValEx(TlaStr), expected NameEx
              builder.bool(true),
          )
      )
    }

    // test fail on scope error
    assertThrows[TBuilderScopeException] {
      build(
          method(
              builder.name("x", StrT1), // x: Str
              builder.eql(builder.name("x", IntT1), builder.name("x", IntT1)), // x: Int
          )
      )
    }

    // test fail on shadowing
    assertThrows[TBuilderScopeException] {
      build(
          // Op( x, \E x \in S: TRUE)
          method(
              builder.name("x", StrT1),
              builder.exists(
                  builder.name("x", StrT1),
                  builder.name("S", SetT1(StrT1)),
                  builder.bool(true),
              ),
          )
      )
    }
  }

}
