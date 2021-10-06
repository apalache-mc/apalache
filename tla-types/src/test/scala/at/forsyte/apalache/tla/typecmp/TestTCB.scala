package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTCB extends FunSuite with BeforeAndAfter {

  test("Plus") {
    val plus = ArithOp.plusCmp

    val args = Seq(
        TlaInt(1),
        TlaInt(1)
    ) map { ValEx(_)(Typed(IntT1())) }

    val res = plus(args)

    assert(res.contains(IntT1()))

    val utArgs = Seq(
        TlaInt(1),
        TlaInt(1)
    ) map { ValEx(_)(Untyped()) }

    assertThrows[TypingException] {
      plus(utArgs)
    }

    val badArgs = Seq(
        ValEx(TlaInt(1))(Typed(IntT1())),
        ValEx(TlaStr("a"))(Typed(StrT1()))
    )

    val badRes = plus(badArgs)

    assert(badRes.isLeft)

    val tooManyArgs = Seq(
        TlaInt(1),
        TlaInt(1),
        TlaInt(1)
    ) map { ValEx(_)(Typed(IntT1())) }

    val tooManyRes = plus(tooManyArgs)

    assert(tooManyRes.isLeft)
  }

  test("And") {
    val and = BoolOp.andCmp
    val args = Seq(
        TlaBool(true),
        TlaBool(true),
        TlaBool(true),
        TlaBool(true)
    ) map { ValEx(_)(Typed(BoolT1())) }

    val res = and(args)
    val res2 = and(args.take(2))

    assert(res.contains(BoolT1()))
    assert(res2.contains(BoolT1()))

    val utArgs = Seq(
        TlaBool(true),
        TlaBool(true)
    ) map { ValEx(_)(Untyped()) }

    assertThrows[TypingException] {
      and(utArgs)
    }

    val badArgs = Seq(
        ValEx(TlaBool(true))(Typed(BoolT1())),
        ValEx(TlaStr("a"))(Typed(StrT1()))
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
            ValEx(TlaStr("y"))(Typed(StrT1()))
        )(Typed(TupT1(StrT1()))),
        NameEx("z")(Typed(IntT1()))
    )

    val resRec = except(recExceptArgs)
    assert(resRec.contains(recType))
  }

}
