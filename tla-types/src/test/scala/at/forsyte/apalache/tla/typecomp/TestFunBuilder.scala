package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestFunBuilder extends BuilderTest {

  test("enum") {
    type T = Seq[TBuilderInstruction]

    type TParam = Seq[TlaType1]

    implicit val typeSeqGen: Gen[TParam] = for {
      n <- Gen.choose(1, 5)
      seq <- Gen.listOfN(n, singleTypeGen)
    } yield seq

    def mkWellTyped(tparam: TParam): T =
      tparam.zipWithIndex.flatMap { case (tt, i) =>
        Seq(
            builder.str(s"x$i"),
            builder.name(s"S$i", tt),
        )
      }

    def mkIllTyped(@unused tparam: TParam): Seq[T] = Seq.empty

    val resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.rec,
        mkWellTyped,
        { seq => seq },
        { ts =>
          val map = ts.zipWithIndex.foldLeft(SortedMap.empty[String, TlaType1]) { case (m, (t, i)) =>
            m + (s"x$i" -> t)
          }
          RecT1(map)
        },
    )

    checkRun(
        runVariadic(
            builder.recMixed,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.recMixed())
    }

    // test fail on n = 1
    assertThrows[IllegalArgumentException] {
      build(builder.recMixed(builder.str("x")))
    }

    // test fail on repeated key
    assertThrows[IllegalArgumentException] {
      build(builder.recMixed(
              builder.str("k"),
              builder.name("v", IntT1),
              builder.str("k"),
              builder.name("w", IntT1),
          ))
    }

    // now for builder.enum (not enumMixed)

    type T2 = Seq[(String, TBuilderInstruction)]

    def mkWellTyped2(tparam: TParam): T2 =
      tparam.zipWithIndex.map { case (tt, i) =>
        s"x$i" ->
          builder.name(s"S$i", tt)
      }

    def mkIllTyped2(@unused tparam: TParam): Seq[T2] = Seq.empty

    val resultIsExpected2 = expectEqTyped[TParam, T2](
        TlaFunOper.rec,
        mkWellTyped2,
        { seq => seq.flatMap { case (s, x) => Seq(builder.str(s), x) } },
        { ts =>
          val map = ts.zipWithIndex.foldLeft(SortedMap.empty[String, TlaType1]) { case (m, (t, i)) =>
            m + (s"x$i" -> t)
          }
          RecT1(map)
        },
    )

    checkRun(
        runVariadic(
            builder.rec,
            mkWellTyped2,
            mkIllTyped2,
            resultIsExpected2,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.rec())
    }

    // test fail on repeated key
    assertThrows[IllegalArgumentException] {
      build(builder.rec(
              ("k", builder.name("v", IntT1)),
              ("k", builder.name("w", IntT1)),
          ))
    }
  }

  test("tuple") {
    type T = Seq[TBuilderInstruction]

    type TParam = Seq[TlaType1]

    implicit val typeSeqGen: Gen[TParam] = for {
      n <- Gen.choose(0, 5)
      seq <- Gen.listOfN(n, singleTypeGen)
    } yield seq

    def mkWellTyped(tparam: TParam): T =
      tparam.zipWithIndex.map { case (tt, i) =>
        builder.name(s"t$i", tt)
      }

    def mkIllTyped(@unused tparam: TParam): Seq[T] = Seq.empty

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.tuple,
        mkWellTyped,
        liftBuildToSeq,
        ts => TupT1(ts: _*),
    )

    checkRun(
        runVariadic(
            builder.tuple,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("seq") {
    type T = Seq[TBuilderInstruction]
    def mkWellTyped(n: Int)(tt: TlaType1): T =
      (1 to n).map { i => builder.name(s"x$i", tt) }
    def mkIllTyped(n: Int)(tt: TlaType1): Seq[T] =
      if (n > 1)
        Seq(
            builder.name("x1", InvalidTypeMethods.differentFrom(tt)) +: (2 to n).map { i =>
              builder.name(s"x$i", tt)
            }
        )
      else Seq.empty

    def resultIsExpected(n: Int) = expectEqTyped[TlaType1, T](
        TlaFunOper.tuple,
        mkWellTyped(n),
        liftBuildToSeq,
        tt => SeqT1(tt),
    )

    def run(tparam: TlaType1) = {
      (1 to 5).forall { n =>
        runVariadic[TlaType1, TBuilderInstruction](
            builder.seq(_: _*),
            mkWellTyped(n),
            mkIllTyped(n),
            resultIsExpected(n),
        )(tparam)
      }
    }

    checkRun(run)

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.seq())
    }
  }

  test("emptySeq") {

    def run(tt: TlaType1): Boolean = {
      val empty: TlaEx = builder.emptySeq(tt)

      assert(
          empty.eqTyped(
              OperEx(TlaFunOper.tuple)(Typed(SeqT1(tt)))
          )
      )
      true
    }

    checkRun(run)
  }

  test("funDef") {
    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)

    type TParam = (TlaType1, TlaType1)

    def mkWellTyped(tparam: TParam): T = {
      val (t, tt) = tparam
      (
          builder.name("e", t),
          builder.name("x", tt),
          builder.name("S", SetT1(tt)),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, tt) = tparam
      Seq(
          (
              builder.name("e", t),
              builder.name("x", InvalidTypeMethods.differentFrom(tt)),
              builder.name("S", SetT1(tt)),
          ),
          (
              builder.name("e", t),
              builder.name("x", tt),
              builder.name("S", InvalidTypeMethods.notSet),
          ),
          (
              builder.name("e", t),
              builder.name("x", tt),
              builder.name("S", SetT1(InvalidTypeMethods.differentFrom(tt))),
          ),
      )
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.funDef,
        mkWellTyped,
        { case (a, b, c) => Seq(a, b, c) },
        { case (a, b) => FunT1(b, a) },
    )

    checkRun(
        runTernary(
            builder.funDef,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // Check scope validation works
    assertThrows[TBuilderScopeException] {
      // [x \in S |-> x]
      build(builder.funDef(
              builder.name("x", StrT1),
              builder.name("x", IntT1),
              builder.name("S", SetT1(IntT1)),
          ))
    }
  }

  /////////////////////////////
  // overloaded method tests //
  /////////////////////////////

  type TParam = (TlaType1, TBuilderInstruction)

  // unsafe for non-applicative
  def argGen(appT: TlaType1): Gen[TBuilderInstruction] = (appT: @unchecked) match {
    case FunT1(a, _) => Gen.const(builder.name("x", a))
    case TupT1(args @ _*) => // assume nonempty
      Gen.choose[BigInt](1, args.size).map(builder.int)
    case RecT1(flds) => // assume nonempty
      Gen.oneOf(flds.keys).map(builder.str)
    case _: SeqT1 => Gen.const(builder.name("x", IntT1))
  }

  implicit val applicativeGen: Gen[TParam] = for {
    appT <- Gen.oneOf(tt1gen.genFun, tt1gen.genRec, tt1gen.genSeq, tt1gen.genTup)
    arg <- argGen(appT)
  } yield (appT, arg)

  test("app") {
    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tparam: TParam): T = {
      val (appT, arg) = tparam
      (
          builder.name("f", appT),
          arg,
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (appT, arg) = tparam
      val Applicative(fromT, _) = Applicative.asInstanceOfApplicative(appT, arg).get
      def nonLiteral(bi: TBuilderInstruction): TBuilderInstruction = bi.map {
        case ex: ValEx => NameEx("x")(ex.typeTag)
        case ex        => ex
      }

      val nonLiteralOpt =
        if (appT.isInstanceOf[RecT1] || appT.isInstanceOf[TupT1])
          Some(
              (
                  builder.name("f", appT),
                  nonLiteral(arg),
              )
          )
        else None

      Seq(
          (
              builder.name("f", InvalidTypeMethods.notApplicative),
              arg,
          ),
          (
              builder.name("f", appT),
              builder.name("x", InvalidTypeMethods.differentFrom(fromT)),
          ),
      ) :++ nonLiteralOpt
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.app,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        { case (appT, arg) => Applicative.asInstanceOfApplicative(appT, arg).get.toT },
    )

    checkRun(
        runBinary(
            builder.app,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("dom") {
    type T = TBuilderInstruction

    def mkWellTyped(tparam: TParam): T = {
      val (appT, _) = tparam
      builder.name("f", appT)
    }

    def mkIllTyped(@unused tparam: TParam): Seq[T] = Seq(
        builder.name("f", InvalidTypeMethods.notApplicative)
    )

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.domain,
        mkWellTyped,
        { a => Seq(a) },
        { case (appT, _) => SetT1(Applicative.domainElemType(appT).get) },
    )

    checkRun(
        runUnary(
            builder.dom,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("except") {
    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tparam: TParam): T = {
      val (appT, arg) = tparam
      (
          builder.name("f", appT),
          arg,
          builder.name("e", Applicative.asInstanceOfApplicative(appT, arg).get.toT),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (appT, arg) = tparam
      val Applicative(fromT, toT) = Applicative.asInstanceOfApplicative(appT, arg).get
      def nonLiteral(bi: TBuilderInstruction): TBuilderInstruction = bi.map {
        case ex: ValEx => NameEx("x")(ex.typeTag)
        case ex        => ex
      }

      val nonLiteralOpt =
        if (appT.isInstanceOf[RecT1] || appT.isInstanceOf[TupT1])
          Some(
              (
                  builder.name("f", appT),
                  nonLiteral(arg),
                  builder.name("e", toT),
              )
          )
        else None

      Seq(
          (
              builder.name("f", InvalidTypeMethods.notApplicative),
              arg,
              builder.name("e", toT),
          ),
          (
              builder.name("f", appT),
              builder.name("x", InvalidTypeMethods.differentFrom(fromT)),
              builder.name("e", toT),
          ),
          (
              builder.name("f", appT),
              arg,
              builder.name("e", InvalidTypeMethods.differentFrom(toT)),
          ),
      ) :++ nonLiteralOpt
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.except,
        mkWellTyped,
        { case (a, b, c) => Seq(a, b, c) },
        { case (appT, _) => appT },
    )

    checkRun(
        runTernary(
            builder.except,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

}
