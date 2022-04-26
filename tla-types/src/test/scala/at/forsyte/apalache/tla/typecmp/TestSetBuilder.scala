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

  test("enumSet/emptySet") {
    val oper = TlaSetOper.enumSet
    val cmp = sigGen.computationFromSignature(oper)

    def mkVar(t: TlaType1)(i: Int): NameWrapper = builder.name(s"a_$i", t)

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

        resEx shouldBe
          OperEx(
              TlaSetOper.enumSet,
              argsAsEx: _*
          )(Typed(SetT1(tt)))

        val badArg0 = mkVar(badType)(0)
        if (i != n) { // i = n means |S| = 1, can't have type errors
          assertThrows[BuilderTypeException] {
            build(builder.enumSet(badArg0, partialArgs: _*))
          }
        }
      }

      val empty: TlaEx = builder.emptySet(tt)

      empty shouldBe OperEx(
          TlaSetOper.enumSet
      )(Typed(SetT1(tt)))

      true
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

}
