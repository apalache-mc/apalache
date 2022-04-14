package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir.{oper, _}
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaFunOper}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTCB extends AnyFunSuite with BeforeAndAfter {

  var varPool = new TypeVarPool()
  var sigGen = new SignatureGenerator(varPool)
  var builder = new TypeCalculatingBuilder(sigGen)

  before {
    varPool = new TypeVarPool()
    sigGen = new SignatureGenerator(varPool)
    builder = new TypeCalculatingBuilder(sigGen)
  }

  test("Plus") {
    val plusCmp = sigGen.computationFromSignatureForFixedArity(TlaArithOper.plus)

    val args = Seq(
        TlaInt(1),
        TlaInt(1),
    ).map { ValEx(_)(Typed(IntT1())) }

    val res = plusCmp(args)

    assert(res.contains(IntT1()))

    val Seq(x, y) = args
    val plusEx = builder.plus(x, y)

    assert(plusEx.eqTyped(OperEx(TlaArithOper.plus, x, y)(Typed(IntT1()))))

    val utArgs = Seq(
        TlaInt(1),
        TlaInt(1),
    ).map { ValEx(_)(Untyped()) }

    assertThrows[TypingException] {
      plusCmp(utArgs)
    }

    val badArgs = Seq(
        ValEx(TlaInt(1))(Typed(IntT1())),
        ValEx(TlaStr("a"))(Typed(StrT1())),
    )

    val badRes = plusCmp(badArgs)

    assert(badRes.isLeft)

    val tooManyArgs = Seq(
        TlaInt(1),
        TlaInt(1),
        TlaInt(1),
    ).map { ValEx(_)(Typed(IntT1())) }

    val tooManyRes = plusCmp(tooManyArgs)

    assert(tooManyRes.isLeft)

    val binaryIntOpers =
      Seq(
          TlaArithOper.minus,
          TlaArithOper.mult,
          TlaArithOper.div,
          TlaArithOper.mod,
      )

    binaryIntOpers.foreach { op =>
      val cmp = sigGen.computationFromSignatureForFixedArity(op)
      val res = cmp(args)
      assert(res.contains(IntT1()))
    }

  }

  test("And") {
    val and = BoolOp.andCmp
    val args = Seq(
        TlaBool(true),
        TlaBool(true),
        TlaBool(true),
        TlaBool(true),
    ).map { ValEx(_)(Typed(BoolT1())) }

    val res = and(args)
    val res2 = and(args.take(2))

    assert(res.contains(BoolT1()))
    assert(res2.contains(BoolT1()))

    val utArgs = Seq(
        TlaBool(true),
        TlaBool(true),
    ).map { ValEx(_)(Untyped()) }

    assertThrows[TypingException] {
      and(utArgs)
    }

    val badArgs = Seq(
        ValEx(TlaBool(true))(Typed(BoolT1())),
        ValEx(TlaStr("a"))(Typed(StrT1())),
    )

    val badRes = and(badArgs)

    assert(badRes.isLeft)

  }

  test("Except") {
    val except = FunOp.exceptCmp

    val recType = RecT1("y" -> IntT1())
    val recExceptArgs = Seq(
        NameEx("x")(Typed(recType)),
        OperEx(
            TlaFunOper.tuple,
            ValEx(TlaStr("y"))(Typed(StrT1())),
        )(Typed(TupT1(StrT1()))),
        NameEx("z")(Typed(IntT1())),
    )

    val resRec = except(recExceptArgs)
    assert(resRec.contains(recType))
  }

}
