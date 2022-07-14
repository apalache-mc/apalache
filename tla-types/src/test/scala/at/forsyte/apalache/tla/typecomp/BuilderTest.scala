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
        Gen.choose[Int](1, args.size).map(builder.int)
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
  implicit val intToBuilderI: Int => TBuilderInstruction = builder.int

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
  def checkRun[TypeParameterization](
      run: TypeParameterization => Boolean
    )(implicit typegen: Gen[TypeParameterization]): Unit = {
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
