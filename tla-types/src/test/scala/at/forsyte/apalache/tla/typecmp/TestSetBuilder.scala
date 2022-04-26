package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import org.scalacheck.Prop.forAll

/**
 * @author
 *   Jure Kukovec
 */
class TestSetBuilder extends BuilderTest {

  val typegen: TlaType1Gen = new TlaType1Gen {}
  def mkVar(t: TlaType1)(i: Int): NameWrapper = builder.name(s"a_$i", t)

  def testBinary(
      oper: TlaSetOper,
      mkLeft: TlaType1 => BuilderWrapper,
      mkRight: TlaType1 => BuilderWrapper,
      method: (BuilderWrapper, BuilderWrapper) => BuilderWrapper,
      expectedResT: TlaType1 => TlaType1): Unit = {
    val cmp = sigGen.computationFromSignature(oper)

    val prop = forAll(typegen.genPrimitiveMono) { tt =>
      val badType = if (tt == IntT1()) StrT1() else IntT1()
      val left = mkLeft(tt)
      val right = mkRight(tt)
      val expectedT = expectedResT(tt)

      val argsAsEx: Seq[TlaEx] = Seq(left, right)
      val res = cmp(argsAsEx)

      assert(res.contains(expectedT))

      val resEx: TlaEx = method(left, right)

      assert(
          resEx.eqTyped(
              OperEx(
                  oper,
                  argsAsEx: _*
              )(Typed(expectedT))
          )
      )

      val badArg = mkLeft(badType)
      assertThrows[BuilderTypeException] {
        build(method(badArg, right))
      }

      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  def testUnary(
      oper: TlaSetOper,
      mkArg: TlaType1 => BuilderWrapper,
      method: BuilderWrapper => BuilderWrapper,
      expectedResT: TlaType1 => TlaType1): Unit = {
    val cmp = sigGen.computationFromSignature(oper)

    val prop = forAll(typegen.genPrimitiveMono) { tt =>
      val badType = IntT1()
      val arg = mkArg(tt)
      val expectedT = expectedResT(tt)

      val res = cmp(Seq(build(arg)))

      assert(res.contains(expectedT))

      val resEx: TlaEx = method(arg)

      assert(
          resEx.eqTyped(
              OperEx(
                  oper,
                  arg,
              )(Typed(expectedT))
          )
      )

      val badArg = arg.map { _.withTag(Typed(badType)) }
      assertThrows[BuilderTypeException] {
        build(method(badArg))
      }

      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("enumSet/emptySet") {
    val oper = TlaSetOper.enumSet
    val cmp = sigGen.computationFromSignature(oper)

    val prop = forAll(typegen.genPrimitiveMono) { tt =>
      val badType = if (tt == IntT1()) StrT1() else IntT1()
      val mkVarTT = mkVar(tt) _
      val arg0: BuilderWrapper = mkVarTT(0)
      val n = 5

      val args: Seq[BuilderWrapper] = (1 to n).map { mkVarTT }.map(generalizeWrapperN)

      (0 to n).foreach { i =>
        val partialArgs = args.dropRight(i)
        val argsAsEx: Seq[TlaEx] = arg0 +: partialArgs
        val res = cmp(argsAsEx)

        assert(res.contains(SetT1(tt)))

        val resEx: TlaEx = builder.enumSet(arg0, partialArgs: _*)

        assert(
            resEx.eqTyped(
                OperEx(
                    TlaSetOper.enumSet,
                    argsAsEx: _*
                )(Typed(SetT1(tt)))
            )
        )

        val badArg0 = mkVar(badType)(0)
        if (i != n) { // i = n means |S| = 1, can't have type errors
          assertThrows[BuilderTypeException] {
            build(builder.enumSet(badArg0, partialArgs: _*))
          }
        }
      }

      val empty: TlaEx = builder.emptySet(tt)

      assert(
          empty.eqTyped(
              OperEx(
                  TlaSetOper.enumSet
              )(Typed(SetT1(tt)))
          )
      )

      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("(not)in") {

    def mkLeft(tt: TlaType1): BuilderWrapper = builder.name("x", tt)
    def mkRight(tt: TlaType1): BuilderWrapper = builder.name("S", SetT1(tt))

    def run(op: TlaSetOper, method: (BuilderWrapper, BuilderWrapper) => BuilderWrapper): Unit =
      testBinary(
          op,
          mkLeft,
          mkRight,
          method,
          _ => BoolT1(),
      )

    run(TlaSetOper.in, builder.in)
    run(TlaSetOper.notin, builder.notin)
  }

  test("cap/cup") {

    def run(oper: TlaSetOper, method: (BuilderWrapper, BuilderWrapper) => BuilderWrapper): Unit =
      testBinary(
          oper,
          tt => builder.name("S", SetT1(tt)),
          tt => builder.name("T", SetT1(tt)),
          method,
          tt => SetT1(tt),
      )

    run(TlaSetOper.cap, builder.cap)
    run(TlaSetOper.cup, builder.cup)
  }

  test("UNION/SUBSET") {

    testUnary(
        TlaSetOper.union,
        tt => builder.name("S", SetT1(SetT1(tt))),
        builder.union,
        tt => SetT1(tt),
    )

    testUnary(
        TlaSetOper.powerset,
        tt => builder.name("S", SetT1(tt)),
        builder.powSet,
        tt => SetT1(SetT1(tt)),
    )
  }
}
