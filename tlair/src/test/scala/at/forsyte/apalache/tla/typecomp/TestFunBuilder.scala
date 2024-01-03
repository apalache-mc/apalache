package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestFunBuilder extends BuilderTest {

  test("enum (rec)") {
    type T = Seq[TBuilderInstruction]

    type TParam = Seq[TlaType1]

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
        ToSeq.variadic,
        { ts =>
          val map = ts.zipWithIndex.foldLeft(SortedMap.empty[String, TlaType1]) { case (m, (t, i)) =>
            m + (s"x$i" -> t)
          }
          RecT1(map)
        },
    )

    checkRun(Generators.nonEmptySeqOfTypesGen)(
        runVariadic(
            builder.recMixed,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // test succeed on n = 0, the empty record
    assert(build(builder.recMixed()).typeTag match {
      case Typed(RecT1(map)) => map.isEmpty
      case _                 => false
    })

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

    // test fail on non-literal key
    assertThrows[IllegalArgumentException] {
      build(builder.recMixed(
              builder.name("k", StrT1),
              builder.name("v", IntT1),
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
        ToSeq.variadicPairs,
        { ts =>
          val map = ts.zipWithIndex.foldLeft(SortedMap.empty[String, TlaType1]) { case (m, (t, i)) =>
            m + (s"x$i" -> t)
          }
          RecT1(map)
        },
    )

    checkRun(Generators.nonEmptySeqOfTypesGen)(
        runVariadic(
            builder.rec,
            mkWellTyped2,
            mkIllTyped2,
            resultIsExpected2,
        )
    )

    // test succeed on n = 0, the empty record
    assert(build(builder.rec()).typeTag match {
      case Typed(RecT1(map)) => map.isEmpty
      case _                 => false
    })

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

    def mkWellTyped(tparam: TParam): T =
      tparam.zipWithIndex.map { case (tt, i) =>
        builder.name(s"t$i", tt)
      }

    def mkIllTyped(@unused tparam: TParam): Seq[T] = Seq.empty

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.tuple,
        mkWellTyped,
        ToSeq.variadic,
        ts => TupT1(ts: _*),
    )

    checkRun(Generators.seqOfTypesGen)(
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
        ToSeq.variadic,
        tt => SeqT1(tt),
    )

    def run(tparam: TlaType1) = {
      (1 to 5).forall { n =>
        runVariadic(
            builder.seq,
            mkWellTyped(n),
            mkIllTyped(n),
            resultIsExpected(n),
        )(tparam)
      }
    }

    checkRun(Generators.singleTypeGen)(run)

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

    checkRun(Generators.singleTypeGen)(run)
  }

  test("funDef") {
    type T = (TBuilderInstruction, Seq[(TBuilderInstruction, TBuilderInstruction)])

    type TParam = (TlaType1, Seq[TlaType1])

    def mkWellTyped(tparam: TParam): T = {
      val (t, ts) = tparam
      (
          builder.name("e", t),
          ts.zipWithIndex.map { case (tt, i) =>
            (
                builder.name(s"x$i", tt),
                builder.name(s"S$i", SetT1(tt)),
            )
          },
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, ts) = tparam
      ts.indices.flatMap { j =>
        Seq(
            (
                builder.name("e", t),
                ts.zipWithIndex.map { case (tt, i) =>
                  (
                      builder.name(s"x$i", if (i == j) InvalidTypeMethods.differentFrom(tt) else tt),
                      builder.name(s"S$i", SetT1(tt)),
                  )
                },
            ),
            (
                builder.name("e", t),
                ts.zipWithIndex.map { case (tt, i) =>
                  (
                      builder.name(s"x$i", tt),
                      builder.name(s"S$i", if (i == j) InvalidTypeMethods.notSet else SetT1(tt)),
                  )
                },
            ),
        )
      }
    }

    def funT(t: TlaType1, ts: Seq[TlaType1]): TlaType1 = ts match {
      case Seq(elem) => FunT1(elem, t)
      case seq       => FunT1(TupT1(seq: _*), t)
    }

    val resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.funDef,
        mkWellTyped,
        ToSeq.variadicPairsWithDistinguishedFirst,
        { case (t, ts) => funT(t, ts) },
    )

    checkRun(Generators.typeAndNonemptySeqGen)(
        runVariadicWithDistinguishedFirst(
            builder.funDef,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // throws on n = 0
    assertThrows[IllegalArgumentException] {
      build(
          builder.funDef(builder.int(1))
      )
    }

    // throws on duplicate vars
    assertThrows[IllegalArgumentException] {
      build(
          builder.funDef(
              builder.name("e", IntT1),
              (
                  builder.name(s"x1", IntT1),
                  builder.name(s"S1", SetT1(IntT1)),
              ),
              (
                  builder.name(s"x1", IntT1),
                  builder.name(s"S2", SetT1(IntT1)),
              ),
          )
      )
    }

    assertThrowsBoundVarIntroductionTernary { case (variable, set, expr) => builder.funDef(expr, (variable, set)) }

    // throws on shadowing: multi-arity
    assertThrows[TBuilderScopeException] {
      build(
          // [ x \in S, y \in T |-> \E y \in T: TRUE ]
          builder.funDef(
              builder.exists(
                  builder.name("y", IntT1),
                  builder.name("T", SetT1(IntT1)),
                  builder.bool(true),
              ),
              (
                  builder.name("x", StrT1),
                  builder.name("S", SetT1(StrT1)),
              ),
              (
                  builder.name("y", IntT1),
                  builder.name("T", SetT1(IntT1)),
              ),
          )
      )
    }

    // does not throw on non-shadowing: multi-arity
    // [ x \in S, y \in {z \in T: \E x \in S: TRUE} |->e ]
    build(
        builder.funDef(
            builder.name("e", StrT1),
            (
                builder.name("x", StrT1),
                builder.name("S", SetT1(StrT1)),
            ),
            (
                builder.name("y", IntT1),
                builder.filter(
                    builder.name("z", IntT1),
                    builder.name("T", SetT1(IntT1)),
                    builder.exists(
                        builder.name("x", StrT1),
                        builder.name("S", SetT1(StrT1)),
                        builder.bool(true),
                    ),
                ),
            ),
        )
    )

    // funDefMixed
    type T2 = (TBuilderInstruction, Seq[TBuilderInstruction])

    def mkWellTyped2(tparam: TParam): T2 = {
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

    def mkIllTyped2(tparam: TParam): Seq[T2] = {
      val (t, ts) = tparam
      ts.indices.flatMap { j =>
        Seq(
            (
                builder.name("e", t),
                ts.zipWithIndex.flatMap { case (tt, i) =>
                  Seq(
                      builder.name(s"x$i", if (i == j) InvalidTypeMethods.differentFrom(tt) else tt),
                      builder.name(s"S$i", SetT1(tt)),
                  )
                },
            ),
            (
                builder.name("e", t),
                ts.zipWithIndex.flatMap { case (tt, i) =>
                  Seq(
                      builder.name(s"x$i", tt),
                      builder.name(s"S$i", if (i == j) InvalidTypeMethods.notSet else SetT1(tt)),
                  )
                },
            ),
        )
      }
    }

    val resultIsExpected2 = expectEqTyped[TParam, T2](
        TlaFunOper.funDef,
        mkWellTyped2,
        ToSeq.variadicWithDistinguishedFirst,
        { case (t, ts) => funT(t, ts) },
    )

    checkRun(Generators.typeAndNonemptySeqGen)(
        runVariadicWithDistinguishedFirst(
            builder.funDefMixed,
            mkWellTyped2,
            mkIllTyped2,
            resultIsExpected2,
        )
    )

    // throws on n = 0
    assertThrows[IllegalArgumentException] {
      build(
          builder.funDefMixed(builder.int(1))
      )
    }

    // throws on duplicate vars
    assertThrows[IllegalArgumentException] {
      build(
          builder.funDefMixed(
              builder.name("e", IntT1),
              builder.name(s"x1", IntT1),
              builder.name(s"S1", SetT1(IntT1)),
              builder.name(s"x1", IntT1),
              builder.name(s"S2", SetT1(IntT1)),
          )
      )
    }

    assertThrowsBoundVarIntroductionTernary { case (variable, set, expr) => builder.funDefMixed(expr, variable, set) }

    // throws on shadowing: multi-arity
    assertThrows[TBuilderScopeException] {
      build(
          // { \E y \in T: TRUE : x \in S, y \in T }
          builder.funDefMixed(
              builder.exists(
                  builder.name("y", IntT1),
                  builder.name("T", SetT1(IntT1)),
                  builder.bool(true),
              ),
              builder.name("x", StrT1),
              builder.name("S", SetT1(StrT1)),
              builder.name("y", IntT1),
              builder.name("T", SetT1(IntT1)),
          )
      )
    }

    // does not throw on non-shadowing: multi-arity
    // [ x \in S, y \in {z \in T: \E x \in S: TRUE} |->e ]
    build(
        builder.funDefMixed(
            builder.name("e", StrT1),
            builder.name("x", StrT1),
            builder.name("S", SetT1(StrT1)),
            builder.name("y", IntT1),
            builder.filter(
                builder.name("z", IntT1),
                builder.name("T", SetT1(IntT1)),
                builder.exists(
                    builder.name("x", StrT1),
                    builder.name("S", SetT1(StrT1)),
                    builder.bool(true),
                ),
            ),
        )
    )

  }

  /////////////////////////////
  // overloaded method tests //
  /////////////////////////////

  type TParam = (TlaType1, TBuilderInstruction)

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
        ToSeq.binary,
        { case (appT, arg) => Applicative.asInstanceOfApplicative(appT, arg).get.toT },
    )

    checkRun(Generators.applicativeAndArgGen)(
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
        ToSeq.unary,
        { case (appT, _) => SetT1(Applicative.domainElemType(appT).get) },
    )

    checkRun(Generators.applicativeAndArgGen)(
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

    def tuplifyArg(ex: TBuilderInstruction): TBuilderInstruction = builder.tuple(ex)

    def mkWellTyped(tparam: TParam): T = {
      val (appT, arg) = tparam
      (
          builder.name("f", appT),
          arg,
          builder.name("e", Applicative.asInstanceOfApplicative(appT, arg).get.toT),
      )
    }

    def wellTypedTuplified(tparam: TParam): T = {
      val (a, b, c) = mkWellTyped(tparam)
      (a, tuplifyArg(b), c)
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
        wellTypedTuplified,
        ToSeq.ternary,
        { case (appT, _) => appT },
    )

    checkRun(Generators.applicativeAndArgGen)(
        runTernary(
            builder.except,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("Regression for #2551: the same free variable name bound in independent function heads do not interfere") {
    val builder = new ScopedBuilder()
    val v = builder.name("x", IntT1)
    val _1 = builder.int(1)
    val intS = builder.intSet()
    // Two independent functions of the form [x \in Int |-> 1]
    val f1 = builder.funDef(_1, (v, intS))
    val f2 = builder.funDef(_1, (v, intS))
    // We should be able to construct a two item set, including these two functions
    val setEx: TlaEx = build(builder.enumSet(f1, f2))
    assert(setEx.typeTag == Typed(SetT1(FunT1(IntT1, IntT1))))
  }

}
