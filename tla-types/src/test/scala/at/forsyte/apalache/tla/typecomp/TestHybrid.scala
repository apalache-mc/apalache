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
              )(Typed(BoolT1))
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
    type TParam = (TlaType1, Seq[(TlaType1, Int)])

    val parameterTypeGen: Gen[(TlaType1, Int)] = for {
      n <- Gen.choose(1, 5)
      ts <- Gen.listOfN(n, tt1gen.genPrimitive)
    } yield (
        ts match {
          case head :: Nil  => head
          case head :: tail => OperT1(tail, head)
          case Nil          => IntT1 // impossible, since 1 <= n <= 5, but the compiler doesn't know and complains
        },
        n - 1,
    )

    implicit val typeSeqGen: Gen[TParam] = for {
      t <- singleTypeGen
      n <- Gen.choose(0, 5)
      seq <- Gen.listOfN(n, parameterTypeGen)
    } yield (t, seq)

    // A(p1,...,pn) == CHOOSE x: p1 /\  p2 >= 0 /\ ... /\ pn = pn
    def mkWellTyped(tparam: TParam): (T, T) = {
      val (t, ts) = tparam
      val tParams = ts.zipWithIndex.map { case ((tt, _), i) => builder.param(s"p$i", tt) }
      val paramConds = tParams.map { case (OperParam(pName, _), tt) =>
        def n: TBuilderInstruction = builder.name(pName, tt)
        // We can try different expressions for different parameter types, as long as each name is used at least once
        tt match {
          case BoolT1 => n
          case IntT1  => builder.ge(n, builder.int(0))
          case OperT1(from, to) =>
            builder.eql(
                builder.appOp(
                    n,
                    from.zipWithIndex.map { case (fromT, i) => builder.name(s"v${i}_$pName", fromT) }: _*
                ),
                builder.name(s"e_$pName", to),
            )
          case _ => builder.eql(n, n)
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
        val tParams = ts.zipWithIndex.map { case ((tt, _), i) => builder.param(s"p$i", tt) }
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
      val params = ts.zipWithIndex.map { case ((_, arity), i) => OperParam(s"p$i", arity) }
      val bTag = Typed(BoolT1)
      val conds = params.zip(ts).map { case (p, (tt, _)) =>
        def n: NameEx = NameEx(p.name)(Typed(tt))
        tt match {
          case BoolT1 => n
          case IntT1  => OperEx(TlaArithOper.ge, n, ValEx(TlaInt(0))(Typed(IntT1)))(bTag)
          case OperT1(from, to) =>
            OperEx(
                TlaOper.eq,
                OperEx(
                    TlaOper.apply,
                    n +:
                      from.zipWithIndex.map { case (fromT, i) =>
                        NameEx(s"v${i}_${p.name}")(Typed(fromT))
                      }: _*
                )(Typed(to)),
                NameEx(s"e_${p.name}")(Typed(to)),
            )(bTag)
          case _ => OperEx(TlaOper.eq, n, n)(bTag)
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
            TlaOperDecl("A", params.toList, expectedBody)(Typed(OperT1(ts.map(_._1), t)))
        )

      ret
    }

    def run(tparam: TParam): Boolean = {

      val (goodDeclExplicitI, goodDeclImplicitI) = mkWellTyped(tparam)

      val goodDeclExplicit = build(goodDeclExplicitI)
      val goodDeclImplicit = build(goodDeclImplicitI)

      goodDeclExplicit shouldEqual goodDeclImplicit

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

    // throws on illegal parameter type

    assertThrows[TBuilderTypeException] {
      builder.param("x", OperT1(Seq(IntT1), OperT1(Seq.empty, IntT1)))
    }

    assertThrows[TBuilderTypeException] {
      builder.param("x", OperT1(Seq.empty, IntT1))
    }

    // throws if parameter type not in scope

    assertThrows[TBuilderScopeException] {
      build(
          builder.declWithInferredParameterTypes(
              "A",
              builder.name("x", IntT1),
              OperParam("p"),
          )
      )
    }

  }

  test("except") {
    type T = (TBuilderInstruction, Seq[(TBuilderInstruction, TBuilderInstruction)])
    type TParam = (TlaType1, Seq[(TBuilderInstruction, TlaType1)])

    var ctr: Int = 0
    // unsafe for non-applicative
    def argAndCdmTypeGen(appT: TlaType1): Gen[(TBuilderInstruction, TlaType1)] = {
      ctr += 1
      (appT: @unchecked) match {
        case FunT1(a, b) => Gen.const((builder.name(s"x$ctr", a), b))
        case TupT1(args @ _*) => // assume nonempty
          Gen.choose[BigInt](1, args.size).map(i => (builder.int(i), args((i - 1).toInt)))
        case RecT1(flds) => // assume nonempty
          Gen.oneOf(flds.keys).map(k => (builder.str(k), flds(k)))
        case SeqT1(t) => Gen.const((builder.name(s"x$ctr", IntT1), t))
      }
    }

    implicit val typeSeqGen: Gen[TParam] = for {
      t <- Gen.oneOf(tt1gen.genFun, tt1gen.genRec, tt1gen.genSeq, tt1gen.genTup)
      n <- Gen.choose(1, 5)
      seq <- Gen.listOfN(n, argAndCdmTypeGen(t))
    } yield (t, seq)

    def mkWellTyped(tparam: TParam): T = {
      val (t, ts) = tparam
      (
          builder.name("e", t),
          ts.zipWithIndex.map { case ((arg, cdmT), i) =>
            (
                arg,
                builder.name(s"v$i", cdmT),
            )
          },
      )
    }

    def nonLiteral(bi: TBuilderInstruction): TBuilderInstruction = bi.map {
      case ex: ValEx => NameEx("x")(ex.typeTag)
      case ex        => ex
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, ts) = tparam
      ts.indices.flatMap { j =>
        val nonLiteralOpt =
          if (t.isInstanceOf[RecT1] || t.isInstanceOf[TupT1])
            Some(
                (
                    builder.name("e", t),
                    ts.zipWithIndex.map { case ((arg, cdmT), i) =>
                      (
                          if (i == j) nonLiteral(arg)
                          else arg,
                          builder.name(s"S$i", cdmT),
                      )
                    },
                )
            )
          else None

        nonLiteralOpt ++
          Seq(
              (
                  builder.name("e", t),
                  ts.zipWithIndex.map { case ((arg, cdmT), i) =>
                    (
                        arg,
                        builder.name(s"S$i",
                            if (i == j) InvalidTypeMethods.differentFrom(cdmT)
                            else cdmT),
                    )
                  },
              )
          )
      }
    }

    def resultIsExpected(tparam: TParam)(res: TBuilderResult): Boolean = {
      val (t, ts) = tparam
      val expected = ts.zipWithIndex.foldLeft(builder.name("e", t)) { case (partial, ((arg, cdmT), i)) =>
        builder.except(
            partial,
            arg,
            builder.name(s"v$i", cdmT),
        )
      }
      res.eqTyped(expected)
    }

    checkRun(
        runVariadicWithDistinguishedFirst(
            builder.exceptMany,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // throws on n = 0
    assertThrows[IllegalArgumentException] {
      build(
          builder.exceptMany(builder.name("f", builder.parseType("Int -> Int")))
      )
    }
  }

  // TODO: test multi-depth except if we choose to keep the methods after the builder transition.

}
