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

    checkRun(Generators.singleTypeGen)(runBinary(
            builder.primeEq,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        ))
  }

  test("decl") {

    type T = TBuilderOperDeclInstruction
    type TParam = (TlaType1, Seq[TlaType1])

    // A(p1,...,pn) == CHOOSE x: p1 /\  p2 >= 0 /\ ... /\ pn = pn
    def mkWellTyped(tparam: TParam): (T, T) = {
      val (t, ts) = tparam
      val tParams = ts.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }
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
        val tParams = ts.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }
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

    def paramArity(tt: TlaType1): Int = tt match {
      case OperT1(args, _) => args.size
      case _               => 0
    }

    def isExpected(tparam: TParam): TlaOperDecl => Boolean = {
      val (t, ts) = tparam
      val params = ts.zipWithIndex.map { case (tt, i) => OperParam(s"p$i", paramArity(tt)) }
      val bTag = Typed(BoolT1)
      val conds = params.zip(ts).map { case (p, tt) =>
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
            TlaOperDecl("A", params.toList, expectedBody)(Typed(OperT1(ts, t)))
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

    checkRun(Generators.declTypesGen)(run)

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

  // Shared code for tests "letIn1" and "letInN"
  object SharedLetTestCode {
    type T = TBuilderInstruction

    /**
     * Tests the following properties (parameterized by TParam):
     *   - The expression generated by `mkWellTyped` builds without throwing, and satisfies the `isExpected` predicate.
     *   - All expressions generated by `forceScopeException` throw `TBuilderScopeException`
     *
     * Iff the above holds, returns true.
     */
    def runLetTests[TParam](
        mkWellTyped: TParam => T,
        forceScopeException: TParam => Seq[T],
        isExpected: TParam => TlaEx => Boolean,
      )(tparam: TParam): Boolean = {

      val goodDecl = mkWellTyped(tparam)

      isExpected(tparam)(goodDecl) shouldBe true

      val badDecls = forceScopeException(tparam)

      badDecls.foreach { instruction =>
        assertThrows[TBuilderScopeException] {
          build(instruction)
        }
      }
      true
    }
  }

  test("letIn (1 decl)") {
    import SharedLetTestCode._
    type TParam1 = (TlaType1, DeclParamT)

    def mkWellTyped1(tparam: TParam1): T = {
      val (_, (bodyT, paramTs)) = tparam
      // LET F(...) == X IN F
      builder.letIn(
          builder.name("F", OperT1(paramTs, bodyT)),
          builder.decl(
              "F",
              builder.name("X", bodyT),
              paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }: _*
          ),
      )
    }

    // LET-IN cannot be type-incorrect if decl is not, that's tested elsewhere
    // It can, however, shadow operator declarations.
    def forceScopeException1(tparam: TParam1): Seq[T] = {
      val (letT, (bodyT, paramTs)) = tparam
      Seq(
          // LET F(...) == X IN \E F: TRUE, F has a non-operator type
          // \E F doesn't match the type of F in the internal context and should fail
          builder.letIn(
              builder.exists(
                  builder.name("F", InvalidTypeMethods.notOper),
                  builder.bool(true),
              ),
              builder.decl(
                  "F",
                  builder.name("X", bodyT),
                  paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }: _*
              ),
          ),
          // LET F(...) == X IN \E F: TRUE, F has the right type
          // \E F shadows LET F and should fail
          builder.letIn(
              builder.exists(
                  builder.name("F", OperT1(paramTs, bodyT)),
                  builder.bool(true),
              ),
              builder.decl(
                  "F",
                  builder.name("X", bodyT),
                  paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }: _*
              ),
          ),
          // LET F(...) == \E F: TRUE IN e, bound F has a non-operator type
          // \E F doesn't match the type of F in the internal context and should fail
          builder.letIn(
              builder.name("e", letT),
              builder.decl(
                  "F",
                  builder.exists(
                      builder.name("F", InvalidTypeMethods.notOper),
                      builder.bool(true),
                  ),
                  paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }: _*
              ),
          ),
          // LET F(...) == \E F: TRUE IN e, bound F has the correct type
          // \E F shadows LET F and should fail
          builder.letIn(
              builder.name("e", letT),
              builder.decl(
                  "F",
                  builder.exists(
                      builder.name("F", OperT1(paramTs, bodyT)),
                      builder.bool(true),
                  ),
                  paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }: _*
              ),
          ),
          // LET F ==
          //   LET F == X
          //   IN F
          // IN F
          // Inner LET F shadows the outer LET F and should fail
          builder.letIn(
              builder.letIn(
                  builder.name("F", OperT1(paramTs, bodyT)),
                  builder.decl(
                      "F",
                      builder.name("X", bodyT),
                      paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }: _*
                  ),
              ),
              builder.decl(
                  "F",
                  builder.name("X", bodyT),
                  paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }: _*
              ),
          ),
      )
    }

    def isExpected1(tparam: TParam1): TlaEx => Boolean = {
      val (_, (bodyT, paramTs)) = tparam
      val params = paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }
      val letT = OperT1(paramTs, bodyT)
      val expectedBody =
        LetInEx(
            builder.name("F", letT),
            builder.decl("F", builder.name("X", bodyT), params: _*),
        )(Typed(letT))

      expectedBody.eqTyped
    }

    checkRun(Generators.typeAndDeclGen)(runLetTests(mkWellTyped1, forceScopeException1, isExpected1))
  }

  test("letIn (N decls)") {
    import SharedLetTestCode._
    type TParamN = (TlaType1, Seq[DeclParamT])

    def mkWellTypedN(tparam: TParamN): T = {
      val (letT, declTs) = tparam
      // LET F1(...) == X1 IN
      // ...
      // LET FN(...) == XN IN
      // e
      val decls = declTs.zipWithIndex.map { case ((t, ts), j) =>
        val tParams = ts.zipWithIndex.map { case (tt, i) => builder.param(s"p${i}_$j", tt) }
        builder.decl(s"F$j", builder.name(s"X$j", t), tParams: _*)
      }
      builder.letIn(builder.name("e", letT), decls: _*)
    }

    // LET-IN cannot be type-incorrect if decl is not, that's tested elsewhere
    // It can, however, shadow operator declarations.
    def forceScopeExceptionN(tparam: TParamN): Seq[T] = {
      val (letT, declParams) = tparam
      declParams.zipWithIndex.flatMap { case ((bodyT_j, paramTs_j), j) =>
        Seq(
            // LET F1 == X1, ..., FN = XN IN \E Fj: TRUE, Fj has the right type
            // \E Fj shadows LET Fj and should fail
            builder.letIn(
                builder.exists(
                    builder.name(s"F$j", OperT1(paramTs_j, bodyT_j)),
                    builder.bool(true),
                ),
                declParams.zipWithIndex.map { case ((bodyT, paramTs), k) =>
                  builder.decl(
                      s"F$k",
                      builder.name(s"X$k", bodyT),
                      paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p${i}_$k", tt) }: _*
                  )
                }: _*
            ),
            // LET  F1 == X1, ...,  Fj == \E Fj: TRUE, ..., FN = XN IN e, bound Fj has the right type
            // \E Fj shadows LET Fj and should fail
            builder.letIn(
                builder.name("e", letT),
                declParams.zipWithIndex.map { case ((bodyT, paramTs), k) =>
                  builder.decl(
                      s"F$k",
                      if (k == j) builder.exists(builder.name(s"F$j", OperT1(paramTs, bodyT)), builder.bool(true))
                      else builder.name(s"X$k", bodyT),
                      paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p${i}_$k", tt) }: _*
                  )
                }: _*
            ),
        )
      }
    }

    def isExpectedN(tparam: TParamN): TlaEx => Boolean = {
      val (letT, declParams) = tparam
      val decls = declParams.zipWithIndex.map { case ((bodyT, paramTs), j) =>
        val params = paramTs.zipWithIndex.map { case (tt, i) => builder.param(s"p${i}_$j", tt) }
        builder.decl(s"F$j", builder.name(s"X$j", bodyT), params: _*)
      }
      val expectedBody =
        decls.foldRight[TlaEx](builder.name("e", letT)) { case (decl, partial) =>
          LetInEx(partial, decl)(Typed(letT))
        }

      expectedBody.eqTyped
    }

    checkRun(Generators.typeAndListOfDeclsGen)(runLetTests(mkWellTypedN, forceScopeExceptionN, isExpectedN))

    // throws on n = 0
    assertThrows[IllegalArgumentException] {
      builder.letIn(builder.int(0))
    }

  }

  test("except") {
    type T = (TBuilderInstruction, Seq[(TBuilderInstruction, TBuilderInstruction)])
    type TParam = (TlaType1, Seq[(TBuilderInstruction, TlaType1)])

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

    checkRun(Generators.applicativeAndSeqArgCdmGen)(runVariadicWithDistinguishedFirst(
            builder.exceptMany,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        ))

    // throws on n = 0
    assertThrows[IllegalArgumentException] {
      build(
          builder.exceptMany(builder.name("f", builder.parseType("Int -> Int")))
      )
    }
  }

  // TODO: test multi-depth except if we choose to keep the methods after the builder transition.

}
