package at.forsyte.apalache.tla.typecheck

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestType1Parser  extends FunSuite {
  test("Int") {
    val result = Type1Parser("Int")
    assert(IntT1() == result)
  }

  test("Bool") {
    val result = Type1Parser("Bool")
    assert(BoolT1() == result)
  }

  test("Str") {
    val result = Type1Parser("Str")
    assert(StrT1() == result)
  }

  test("var a") {
    val result = Type1Parser("a")
    assert(VarT1("a") == result)
  }

  test("const PID") {
    val result = Type1Parser("PID")
    assert(ConstT1("PID") == result)
  }

  test("Set(Int)") {
    val result = Type1Parser("Set(Int)")
    assert(SetT1(IntT1()) == result)
  }

  test("Seq(Int)") {
    val result = Type1Parser("Seq(Int)")
    assert(SeqT1(IntT1()) == result)
  }

  test("Set(Int) -> Bool") {
    val result = Type1Parser("Set(Int) -> Bool")
    assert(FunT1(SetT1(IntT1()), BoolT1()) == result)
  }

  test("(Set(Int) -> Bool) -> Str") {
    val result = Type1Parser("Set(Int) -> Bool -> Str")
    assert(FunT1(FunT1(SetT1(IntT1()), BoolT1()), StrT1()) == result)
  }

}