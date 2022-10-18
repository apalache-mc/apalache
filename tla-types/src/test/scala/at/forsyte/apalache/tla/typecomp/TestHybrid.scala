package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaOper}
import at.forsyte.apalache.tla.types.tla.TypedParam
import org.junit.runner.RunWith
import org.scalacheck.Prop.forAll
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

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

    checkRun(Generators.singleTypeGen)(
        runBinary(
            builder.primeEq,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("decl") {

    type ExplicitT = (String, TBuilderInstruction, Seq[TypedParam])
    type TParam = (TlaType1, Seq[TlaType1])

    // To test the declaration constructor, we need to test the relation between declared parameters, and the
    // way the parameters are actually used in the declaration body. Concretely, we need to create a declaration body,
    // in which every parameter p, with expected type T, appears in an expression that only permits values of type T.
    // This way, we can test whether the builder correctly detects a discrepancy between p declared with type T
    // and p used with type TT (s.t. TT /= T).
    //
    // We could always just do \E (q: declaredTypeOf(p)): q = p, but in real specs, operator types can't appear like that
    // To test operator parameters with types (a1,...,an) => b, we construct values (q1: a1, ..., qn: an) and (e: b),
    // then test application. For non-operator parameters, we just test \E (q: typeOf(p)): q = p
    def paramCond(param: TypedParam): TBuilderInstruction = {
      val (OperParam(pName, _), tt) = param
      def mkNameTT(s: String) = builder.name(s, tt)
      tt match {
        // given an operator parameter p(_,...,_), returns the term p(v1_p, ...., vn_p) = e_p
        case OperT1(from, to) =>
          builder.eql(
              builder.appOp(
                  mkNameTT(pName),
                  from.zipWithIndex.map { case (fromT, i) => builder.name(s"v${i}_${pName}", fromT) }: _*
              ),
              builder.name(s"e_$pName", to),
          )
        // given a simple parameter p, returns the term \E q: q = p
        case _ =>
          val qName = s"q_$pName"
          builder.exists(
              mkNameTT(qName),
              builder.eql(
                  mkNameTT(qName),
                  mkNameTT(pName),
              ),
          )
      }
    }

    // CHOOSE can make the body type w/e we need it to be
    // A(p1(_,...,_),p2,...,pn) == CHOOSE x: p1(v1_p1,...,vk_p1) = e_p1 /\  \E q2: q2 = p2 /\ ...
    def mkWellTypedExplicit(tparam: TParam): ExplicitT = {
      val (t, ts) = tparam
      val tParams = ts.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }
      (
          "A",
          builder.choose(
              builder.name("x", t),
              builder.and(tParams.map { paramCond }: _*),
          ),
          tParams,
      )
    }

    // No type exception, only scope exceptions
    def mkIllTypedExplicit(@unused tparam: TParam): Seq[ExplicitT] = Seq.empty

    def expectEqTypedDecl[T](
        mkWellTyped: TParam => (String, TBuilderInstruction, T),
        exParams: TParam => List[OperParam],
        exType: TParam => TlaType1): TParam => TlaOperDecl => Boolean = {
      tparam =>
        { resDecl =>
          val (name, body, _) = mkWellTyped(tparam)
          resDecl.eqTyped(
              TlaOperDecl(
                  name,
                  exParams(tparam),
                  body,
              )(Typed(exType(tparam)))
          )
        }
    }

    def paramArity(tt: TlaType1): Int = tt match {
      case OperT1(args, _) => args.size
      case _               => 0
    }

    val resultIsExpectedExplicit = expectEqTypedDecl(
        mkWellTypedExplicit,
        { case (_, ts) => ts.toList.zipWithIndex.map { case (tt, i) => OperParam(s"p$i", paramArity(tt)) } },
        { case (t, ts) => OperT1(ts, t) },
    )

    checkRun(Generators.declTypesGen)(
        runTernary(
            builder.decl,
            mkWellTypedExplicit,
            mkIllTypedExplicit,
            resultIsExpectedExplicit,
        )
    )

    def mkIllScopedExplicit(tparam: TParam): Seq[ExplicitT] = {
      val (t, ts) = tparam
      val tParams = ts.zipWithIndex.map { case (tt, i) => builder.param(s"p$i", tt) }
      val body = builder.choose(
          builder.name("x", t),
          builder.and(tParams.map { paramCond }: _*),
      )
      ts.indices.map { j =>
        (
            "A",
            body,
            ts.zipWithIndex.map { case (tt, i) =>
              // j-th param is used with type tt and declared with something else
              builder.param(s"p$i",
                  if (i == j) InvalidTypeMethods.differentFrom(tt)
                  else tt)
            },
        )
      }
    }

    // TODO: refactor after #1965
    val scopeExcProp = forAll(Generators.declTypesGen) { tparam =>
      mkIllScopedExplicit(tparam).foreach { case (name, body, params) =>
        assertThrows[TBuilderScopeException] {
          build(
              builder.decl(name, body, params: _*)
          )
        }
      }
      true
    }
    check(scopeExcProp, minSuccessful(1000), sizeRange(8))

    // Now check the implicit variant

    type ImplicitT = (String, TBuilderInstruction, Seq[OperParam])
    def mkWellTypedImplicit(tparam: TParam): ImplicitT = {
      val (name, body, tParams) = mkWellTypedExplicit(tparam)
      (
          name,
          body,
          tParams.map(_._1),
      )
    }

    def mkIllTypedImplicit(@unused tparam: TParam): Seq[ImplicitT] = Seq.empty

    val resultIsExpectedImplicit = expectEqTypedDecl(
        mkWellTypedImplicit,
        { case (_, ts) => ts.toList.zipWithIndex.map { case (tt, i) => OperParam(s"p$i", paramArity(tt)) } },
        { case (t, ts) => OperT1(ts, t) },
    )

    checkRun(Generators.declTypesGen)(
        runTernary(
            builder.declWithInferredParameterTypes,
            mkWellTypedImplicit,
            mkIllTypedImplicit,
            resultIsExpectedImplicit,
        )
    )

    // TODO: refactor after #1965
    // explicit == implicit
    val explicitImplicitProp = forAll(Generators.declTypesGen) { tparam =>
      val (nameE, bodyE, paramsE) = mkWellTypedExplicit(tparam)
      val (nameI, bodyI, paramsI) = mkWellTypedImplicit(tparam)
      build(builder.decl(nameE, bodyE, paramsE: _*)) shouldEqual
        build(builder.declWithInferredParameterTypes(nameI, bodyI, paramsI: _*))
      true
    }
    check(explicitImplicitProp, minSuccessful(1000), sizeRange(8))

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

    checkRun(Generators.applicativeAndSeqArgCdmGen)(
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
          builder.exceptMany(builder.name("f", FunT1(IntT1, IntT1)))
      )
    }
  }

  // TODO: test multi-depth except if we choose to keep the methods after the builder transition.

}
