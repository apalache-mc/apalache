package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestSetBuilder extends BuilderTest {

  test("polyTest") {
    val t = VarT1("c")

    def n_a = builder.name("a", t)

    val r = build(builder.enumSet(n_a, n_a))

    assert(r.typeTag == Typed(SetT1(t)))

  }

  test("enumSet") {
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
        TlaSetOper.enumSet,
        mkWellTyped(n),
        liftBuildToSeq,
        tt => SetT1(tt),
    )

    def run(tparam: TlaType1) = {
      (1 to 5).forall { n =>
        runVariadic[TlaType1, TBuilderInstruction](
            builder.enumSet(_: _*),
            mkWellTyped(n),
            mkIllTyped(n),
            resultIsExpected(n),
        )(tparam)
      }
    }

    checkRun(run)

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.enumSet())
    }
  }

  test("emptySet") {

    def run(tt: TlaType1): Boolean = {
      val empty: TlaEx = builder.emptySet(tt)

      assert(
          empty.eqTyped(
              OperEx(TlaSetOper.enumSet)(Typed(SetT1(tt)))
          )
      )
      true
    }

    checkRun(run)
  }

  test("(not)in") {

    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("x", tt),
          builder.name("S", SetT1(tt)),
      )
    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("x", tt),
              builder.name("S", InvalidTypeMethods.notSet),
          ),
          (
              builder.name("x", InvalidTypeMethods.differentFrom(tt)),
              builder.name("S", SetT1(tt)),
          ),
      )

    def resultIsExpected(op: TlaSetOper) = expectEqTyped[TlaType1, T](
        op,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        _ => BoolT1,
    )

    def run(
        op: TlaSetOper,
        method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction,
      )(tt: TlaType1): Boolean =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(op),
      )(tt)

    checkRun(run(TlaSetOper.in, builder.in))
    checkRun(run(TlaSetOper.notin, builder.notin))
  }

  test("cap/cup/setminus") {

    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("S", SetT1(tt)),
          builder.name("T", SetT1(tt)),
      )
    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("S", InvalidTypeMethods.notSet),
              builder.name("T", SetT1(tt)),
          ),
          (
              builder.name("S", SetT1(InvalidTypeMethods.differentFrom(tt))),
              builder.name("T", SetT1(tt)),
          ),
      )

    def resultIsExpected(op: TlaSetOper) = expectEqTyped[TlaType1, T](
        op,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        tt => SetT1(tt),
    )

    def run(
        op: TlaSetOper,
        method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction,
      )(tt: TlaType1): Boolean =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(op),
      )(tt)

    checkRun(run(TlaSetOper.cap, builder.cap))
    checkRun(run(TlaSetOper.cup, builder.cup))
    checkRun(run(TlaSetOper.setminus, builder.setminus))
  }

  test("union") {

    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T =
      builder.name("S", SetT1(SetT1(tt)))
    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("S", InvalidTypeMethods.notSet),
          builder.name("S", SetT1(InvalidTypeMethods.notSet)),
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaSetOper.union,
        mkWellTyped,
        Seq(_),
        tt => SetT1(tt),
    )

    checkRun(
        runUnary(
            builder.union,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("filter") {

    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("x", tt),
          builder.name("S", SetT1(tt)),
          builder.name("p", BoolT1),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("x", tt),
              builder.name("S", SetT1(tt)),
              builder.name("p", InvalidTypeMethods.notBool),
          ),
          (
              builder.name("x", tt),
              builder.name("S", InvalidTypeMethods.notSet),
              builder.name("p", BoolT1),
          ),
          (
              builder.name("x", InvalidTypeMethods.differentFrom(tt)),
              builder.name("S", SetT1(tt)),
              builder.name("p", BoolT1),
          ),
      )

    val resultIsExpected = expectEqTyped[TlaType1, T](
        TlaSetOper.filter,
        mkWellTyped,
        { case (a, b, c) => Seq(a, b, c) },
        tt => SetT1(tt),
    )

    checkRun(
        runTernary(
            builder.filter,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // thorws on non-name
    assertThrows[IllegalArgumentException] {
      build(
          builder.filter(
              builder.str("x"),
              builder.name("S", SetT1(StrT1)),
              builder.name("p", BoolT1),
          )
      )
    }

  }

  test("map") {
    type T = (TBuilderInstruction, Seq[TBuilderInstruction])

    type TParam = (TlaType1, Seq[TlaType1])

    implicit val typeSeqGen: Gen[TParam] = for {
      t <- singleTypeGen
      n <- Gen.choose(1, 5)
      seq <- Gen.listOfN(n, singleTypeGen)
    } yield (t, seq)

    def mkWellTyped(tparam: TParam): T = {
      val (t, ts) = tparam
      (
          builder.name("e", t),
          ts.zipWithIndex.flatMap { case (tt, i) =>
            Seq(
                builder.name(s"x$i", tt),
                builder.name(s"S$i", SetT1(tt)),
            )
          },
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, ts) = tparam
      Seq(
          (
              builder.name("e", t),
              ts.zipWithIndex.flatMap { case (tt, i) =>
                Seq(
                    builder.name(s"x$i", InvalidTypeMethods.differentFrom(tt)),
                    builder.name(s"S$i", SetT1(tt)),
                )
              },
          ),
          (
              builder.name("e", t),
              ts.zipWithIndex.flatMap { case (tt, i) =>
                Seq(
                    builder.name(s"x$i", tt),
                    builder.name(s"S$i", InvalidTypeMethods.notSet),
                )
              },
          ),
      )
    }

    val resultIsExpected = expectEqTyped[TParam, T](
        TlaSetOper.map,
        mkWellTyped,
        { case (a, seq) => liftBuildToSeq(a +: seq) },
        { case (t, _) => SetT1(t) },
    )

    checkRun(
        runVariadicWithDistinguishedFirst(
            builder.mapMixed,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.mapMixed(builder.name("x", IntT1)))
    }

    // now for builder.map (not mapMixed)

    type T2 = (TBuilderInstruction, Seq[(TBuilderInstruction, TBuilderInstruction)])

    def mkWellTyped2(tparam: TParam): T2 = {
      val (t, ts) = tparam
      (
          builder.name("e", t),
          ts.zipWithIndex.map { case (tt, i) =>
            builder.name(s"x$i", tt) ->
              builder.name(s"S$i", SetT1(tt))
          },
      )
    }

    def mkIllTyped2(tparam: TParam): Seq[T2] = {
      val (t, ts) = tparam
      Seq(
          (
              builder.name("e", t),
              ts.zipWithIndex.map { case (tt, i) =>
                builder.name(s"x$i", InvalidTypeMethods.differentFrom(tt)) ->
                  builder.name(s"S$i", SetT1(tt))
              },
          ),
          (
              builder.name("e", t),
              ts.zipWithIndex.map { case (tt, i) =>
                builder.name(s"x$i", tt) ->
                  builder.name(s"S$i", InvalidTypeMethods.notSet)
              },
          ),
      )
    }

    val resultIsExpected2 = expectEqTyped[TParam, T2](
        TlaSetOper.map,
        mkWellTyped2,
        { case (a, seq) => liftBuildToSeq(a +: seq.flatMap { case (b, c) => Seq(b, c) }) },
        { case (t, _) => SetT1(t) },
    )

    checkRun(
        runVariadicWithDistinguishedFirst(
            builder.map,
            mkWellTyped2,
            mkIllTyped2,
            resultIsExpected2,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.map(builder.name("x", IntT1)))
    }

  }

  test("funSet") {

    type T = (TBuilderInstruction, TBuilderInstruction)
    type TParam = (TlaType1, TlaType1)

    def mkWellTyped(tparam: TParam): T = {
      val (t1, t2) = tparam
      (
          builder.name("S", SetT1(t1)),
          builder.name("T", SetT1(t2)),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t1, _) = tparam
      Seq(
          (
              builder.name("S", SetT1(t1)),
              builder.name("T", InvalidTypeMethods.notSet),
          )
      )
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaSetOper.funSet,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        { case (t1, t2) => SetT1(FunT1(t1, t2)) },
    )

    checkRun(
        runBinary(
            builder.funSet,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("recSet") {
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
            builder.name(s"S$i", SetT1(tt)),
        )
      }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      Seq(
          tparam.zipWithIndex.flatMap { case (_, i) =>
            Seq(
                builder.str(s"x$i"),
                builder.name(s"S$i", InvalidTypeMethods.notSet),
            )
          }
      )
    }

    val resultIsExpected = expectEqTyped[TParam, T](
        TlaSetOper.recSet,
        mkWellTyped,
        { seq => seq },
        { ts =>
          val map = ts.zipWithIndex.foldLeft(SortedMap.empty[String, TlaType1]) { case (m, (t, i)) =>
            m + (s"x$i" -> t)
          }
          SetT1(RecT1(map))
        },
    )

    checkRun(
        runVariadic(
            builder.recSetMixed,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.recSetMixed())
    }

    // test fail on n = 1
    assertThrows[IllegalArgumentException] {
      build(builder.recSetMixed(builder.str("x")))
    }

    // test fail on repeated key
    assertThrows[IllegalArgumentException] {
      build(builder.recSetMixed(
              builder.str("k"),
              builder.name("S", SetT1(IntT1)),
              builder.str("k"),
              builder.name("T", SetT1(IntT1)),
          ))
    }

    // now for builder.map (not mapMixed)

    type T2 = Seq[(String, TBuilderInstruction)]

    def mkWellTyped2(tparam: TParam): T2 =
      tparam.zipWithIndex.map { case (tt, i) =>
        s"x$i" ->
          builder.name(s"S$i", SetT1(tt))
      }

    def mkIllTyped2(tparam: TParam): Seq[T2] = {
      Seq(
          tparam.zipWithIndex.map { case (_, i) =>
            s"x$i" ->
              builder.name(s"S$i", InvalidTypeMethods.notSet)
          }
      )
    }

    val resultIsExpected2 = expectEqTyped[TParam, T2](
        TlaSetOper.recSet,
        mkWellTyped2,
        { seq => seq.flatMap { case (s, x) => Seq(builder.str(s), x) } },
        { ts =>
          val map = ts.zipWithIndex.foldLeft(SortedMap.empty[String, TlaType1]) { case (m, (t, i)) =>
            m + (s"x$i" -> t)
          }
          SetT1(RecT1(map))
        },
    )

    checkRun(
        runVariadic(
            builder.recSet,
            mkWellTyped2,
            mkIllTyped2,
            resultIsExpected2,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.recSet())
    }

    // test fail on repeated key
    assertThrows[IllegalArgumentException] {
      build(builder.recSet(
              ("k", builder.name("S", SetT1(IntT1))),
              ("k", builder.name("T", SetT1(IntT1))),
          ))
    }
  }

  test("seqSet") {
    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T =
      builder.name("S", SetT1(tt))
    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("S", InvalidTypeMethods.notSet)
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaSetOper.seqSet,
        mkWellTyped,
        Seq(_),
        tt => SetT1(SeqT1(tt)),
    )

    checkRun(
        runUnary(
            builder.seqSet,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("subseteq") {

    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("S", SetT1(tt)),
          builder.name("T", SetT1(tt)),
      )
    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("S", InvalidTypeMethods.notSet),
              builder.name("T", SetT1(tt)),
          ),
          (
              builder.name("S", SetT1(InvalidTypeMethods.differentFrom(tt))),
              builder.name("T", SetT1(tt)),
          ),
      )

    val resultIsExpected = expectEqTyped[TlaType1, T](
        TlaSetOper.subseteq,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        _ => BoolT1,
    )

    checkRun(
        runBinary(
            builder.subseteq,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("times") {
    type T = Seq[TBuilderInstruction]

    type TParam = Seq[TlaType1]

    implicit val typeSeqGen: Gen[TParam] = for {
      n <- Gen.choose(2, 5)
      seq <- Gen.listOfN(n, singleTypeGen)
    } yield seq

    def mkWellTyped(tparam: TParam): T =
      tparam.zipWithIndex.map { case (t, i) => builder.name(s"S$i", SetT1(t)) }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      // assume |tparam| >= 2
      Seq(
          builder.name("S1", InvalidTypeMethods.notSet) +: tparam.tail.zipWithIndex.map { case (t, i) =>
            builder.name(s"S${i + 2}", t)
          }
      )
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaSetOper.times,
        mkWellTyped,
        liftBuildToSeq,
        tts => SetT1(TupT1(tts: _*)),
    )

    checkRun(
        runVariadic[TParam, TBuilderInstruction](
            builder.times(_: _*),
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.times())
    }

    // test fail on n = 1
    assertThrows[IllegalArgumentException] {
      build(builder.times(builder.name("x", SetT1(IntT1))))
    }
  }

  test("powSet") {

    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T =
      builder.name("S", SetT1(tt))
    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("S", InvalidTypeMethods.notSet)
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaSetOper.powerset,
        mkWellTyped,
        Seq(_),
        tt => SetT1(SetT1(tt)),
    )

    checkRun(
        runUnary(
            builder.powSet,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

}
