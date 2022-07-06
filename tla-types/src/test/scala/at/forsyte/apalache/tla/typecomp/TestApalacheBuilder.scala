package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestApalacheBuilder extends BuilderTest {

  test("assign") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.prime(builder.name("lhs", tt)),
          builder.name("rhs", tt),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.prime(builder.name("lhs", InvalidTypeMethods.differentFrom(tt))),
              builder.name("rhs", tt),
          ),
          (
              builder.prime(builder.name("lhs", tt)),
              builder.name("rhs", InvalidTypeMethods.differentFrom(tt)),
          ),
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        ApalacheOper.assign,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        _ => BoolT1,
    )

    checkRun(
        runBinary(
            builder.assign,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // Assert throws on non-prime
    assertThrows[IllegalArgumentException] {
      build(
          builder.assign(builder.int(1), builder.int(1))
      )
    }

  }

  test("gen") {

    val gen = Gen.zip(Gen.choose(1, 10), singleTypeGen)

    val prop = forAll(gen) { case (n, tt) =>
      val genEx: TlaEx = builder.gen(n, tt)
      genEx.eqTyped(
          OperEx(
              ApalacheOper.gen,
              builder.int(n),
          )(Typed(tt))
      )
    }
    check(prop, minSuccessful(1000), sizeRange(8))

    assertThrows[IllegalArgumentException] {
      build(
          builder.gen(-1, IntT1)
      )
    }
  }

  test("skolem") {
    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T =
      builder.exists(
          builder.name("x", tt),
          builder.name("S", SetT1(tt)),
          builder.name("p", BoolT1),
      )

    // If ex is not \E, then it's malformed. If it is, it must be Boolean
    def mkIllTyped(@unused tt: TlaType1): Seq[T] = Seq.empty

    def resultIsExpected = expectEqTyped[TlaType1, T](
        ApalacheOper.skolem,
        mkWellTyped,
        Seq(_),
        _ => BoolT1,
    )

    checkRun(
        runUnary(
            builder.skolem,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // throws on non-existential
    assertThrows[IllegalArgumentException] {
      build(
          builder.skolem(builder.bool(true))
      )
    }
  }

  test("guess") {
    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T = builder.name("S", SetT1(tt))

    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("S", InvalidTypeMethods.notSet)
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        ApalacheOper.guess,
        mkWellTyped,
        Seq(_),
        tt => tt,
    )

    checkRun(
        runUnary(
            builder.guess,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("expand") {
    type T = TBuilderInstruction

    // Set variant

    def mkWellTyped1(tt: TlaType1): T =
      builder.powSet(builder.name("S", SetT1(tt)))

    // If ex is not SUBSET, then it's malformed. If it is, it must be a set-of-sets type
    def mkIllTyped1(@unused tt: TlaType1): Seq[T] = Seq.empty

    def resultIsExpected1 = expectEqTyped[TlaType1, T](
        ApalacheOper.expand,
        mkWellTyped1,
        Seq(_),
        tt => SetT1(SetT1(tt)),
    )

    checkRun(
        runUnary(
            builder.expand,
            mkWellTyped1,
            mkIllTyped1,
            resultIsExpected1,
        )
    )

    // throws on non-SUBSET
    assertThrows[IllegalArgumentException] {
      build(
          builder.expand(builder.name("S", SetT1(SetT1(IntT1))))
      )
    }

    // Function variant

    type TParam = (TlaType1, TlaType1)

    def mkWellTyped2(tparam: TParam): T = {
      val (a, b) = tparam
      builder.funSet(builder.name("S", SetT1(a)), builder.name("T", SetT1(b)))
    }

    // If ex is not [A -> B], then it's malformed. If it is, it must be a set-of-fns type
    def mkIllTyped2(@unused tparam: TParam): Seq[T] = Seq.empty

    def resultIsExpected2 = expectEqTyped[TParam, T](
        ApalacheOper.expand,
        mkWellTyped2,
        Seq(_),
        { case (a, b) => SetT1(FunT1(a, b)) },
    )

    checkRun(
        runUnary(
            builder.expand,
            mkWellTyped2,
            mkIllTyped2,
            resultIsExpected2,
        )
    )

    // throws on non-functionset
    assertThrows[IllegalArgumentException] {
      build(
          builder.expand(builder.name("S", SetT1(FunT1(IntT1, IntT1))))
      )
    }
  }

  test("constCard") {
    type T = TBuilderInstruction
    type TParam = (Int, TlaType1)

    implicit val gen: Gen[TParam] = Gen.zip(Gen.choose(0, 10), singleTypeGen)

    def mkWellTyped(tparam: TParam): T = {
      val (n, tt) = tparam
      builder.ge(builder.cardinality(builder.name("S", SetT1(tt))), builder.int(n))
    }

    // If ex is not Cardinality(S) >= k, then it's malformed. If it is, it must be a Boolean
    def mkIllTyped(@unused tparam: TParam): Seq[T] = Seq.empty

    def resultIsExpected = expectEqTyped[TParam, T](
        ApalacheOper.constCard,
        mkWellTyped,
        Seq(_),
        _ => BoolT1,
    )

    checkRun(
        runUnary(
            builder.constCard,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // throws on non-Cardinality
    assertThrows[IllegalArgumentException] {
      build(
          builder.constCard(builder.bool(true))
      )
    }
  }

  // TODO: Implement builder.letInEx, so we can construct lambdas for the following tests
  test("mkSeq") {}
  test("foldSet") {}
  test("foldSeq") {}

  test("setAsFun") {
    type T = TBuilderInstruction
    type TParam = (TlaType1, TlaType1)

    def mkWellTyped(tparam: TParam): T = {
      val (a, b) = tparam
      builder.name("S", SetT1(TupT1(a, b)))
    }

    def mkIllTyped(@unused tparam: TParam): Seq[T] =
      Seq(
          builder.name("S", InvalidTypeMethods.notSet),
          builder.name("S", SetT1(InvalidTypeMethods.notTup)),
      )

    def resultIsExpected = expectEqTyped[TParam, T](
        ApalacheOper.setAsFun,
        mkWellTyped,
        Seq(_),
        { case (a, b) => FunT1(a, b) },
    )

    checkRun(
        runUnary(
            builder.setAsFun,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

}
