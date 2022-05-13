package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaArithOper, TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestHybrid extends BuilderTest {
  test("primeEq") {
    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("x", tt),
          builder.name("y", tt),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("x", InvalidTypeMethods.differentFrom(tt)),
              builder.name("y", tt),
          ),
          (
              builder.name("x", tt),
              builder.name("y", InvalidTypeMethods.differentFrom(tt)),
          ),
      )

    def resultIsExpected: TlaType1 => TBuilderResult => Boolean = {
      tt =>
        { resEx =>
          val (x, y) = mkWellTyped(tt)
          resEx.eqTyped(
              OperEx(
                  TlaOper.eq,
                  OperEx(TlaActionOper.prime, x)(Typed(tt)),
                  y,
              )(Typed(BoolT1()))
          )
        }
    }

    checkRun(
        runBinary(
            builder.primeEq,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("decl") {

    type T = TBuilderOperDeclInstruction
    type TParam = (TlaType1, Seq[TlaType1])

    implicit val typeSeqGen: Gen[TParam] = for {
      t <- singleTypeGen
      n <- Gen.choose(0, 5)
      seq <- Gen.listOfN(n, singleTypeGen)
    } yield (t, seq)

    // A(p1,...,pn) == CHOOSE x: p1 /\  p2 >= 0 /\ ... /\ pn = pn
    def mkWellTyped(tparam: TParam): (T, T) = {
      val (t, ts) = tparam
      val tParams = ts.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt, 0) }
      val paramConds = tParams.map { case (OperParam(pName, _), tt) =>
        def n: TBuilderInstruction = builder.name(pName, tt)
        // We can try different expressions for different parameter types, as long as each name is used at least once
        tt match {
          case BoolT1() => n
          case IntT1()  => builder.ge(n, builder.int(0))
          case _        => builder.eql(n, n)
        }

      }
      val body = builder.choose(
          builder.name("x", t),
          builder.and(paramConds: _*),
      )

      val explicit = builder.decl("A", body, tParams: _*)
      val withParamTypesFromScope =
        builder.declWithInferredParameterTypes("A", body, tParams.map(_._1): _*)

      (explicit, withParamTypesFromScope)
    }

    def forceScopeException(tparam: TParam): Seq[T] = {
      val (t, ts) = tparam
      ts.indices.map { j =>
        val tParams = ts.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt, 0) }
        val eqls = tParams.zipWithIndex.map { case ((OperParam(pName, _), tt), i) =>
          // We use the j-th parameter inconsistently w.r.t. types
          val n = builder.name(pName, if (i != j) tt else InvalidTypeMethods.differentFrom(tt))
          builder.eql(n, n)
        }
        val body = builder.choose(
            builder.name("x", t),
            builder.and(eqls: _*),
        )
        builder.decl("A", body, tParams: _*)
      }
    }

    def isExpected(tparam: TParam): TlaOperDecl => Boolean = {
      val (t, ts) = tparam
      val params = ts.indices.map { i => OperParam(s"p$i", 0) }
      val bTag = Typed(BoolT1())
      val conds = params.zip(ts).map { case (p, tt) =>
        def n: NameEx = NameEx(p.name)(Typed(tt))
        tt match {
          case BoolT1() => n
          case IntT1()  => OperEx(TlaArithOper.ge, n, ValEx(TlaInt(0))(Typed(IntT1())))(bTag)
          case _        => OperEx(TlaOper.eq, n, n)(bTag)
        }
      }
      val tTag = Typed(t)
      val expectedBody =
        OperEx(
            TlaOper.chooseUnbounded,
            NameEx("x")(tTag),
            OperEx(
                TlaBoolOper.and,
                conds: _*
            )(bTag),
        )(tTag)

      def ret(decl: TlaOperDecl): Boolean =
        decl.eqTyped(
            TlaOperDecl("A", params.toList, expectedBody)(Typed(OperT1(ts, t)))
        )

      ret
    }

    def run(tparam: TParam): Boolean = {

      val (goodDeclExplicitI, goodDeclImplicitI) = mkWellTyped(tparam)

      val goodDeclExplicit = build(goodDeclExplicitI)
      val goodDeclImplicit = build(goodDeclImplicitI)

      goodDeclImplicit shouldEqual goodDeclImplicit

      isExpected(tparam)(goodDeclExplicit) shouldBe true

      val badDeclIs = forceScopeException(tparam)

      badDeclIs.foreach { instruction =>
        assertThrows[TBuilderScopeException] {
          build(instruction)
        }
      }

      true
    }

    checkRun(run)

    assertThrows[TBuilderScopeException] {
      build(
          builder.declWithInferredParameterTypes(
              "A",
              builder.name("x", IntT1()),
              OperParam("p"),
          )
      )
    }

  }
}
