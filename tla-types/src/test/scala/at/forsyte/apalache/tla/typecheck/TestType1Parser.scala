package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.typecheck.parser.Type1ParseError
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.SortedMap

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

  test("<<>> is rejected") {
    assertThrows[Type1ParseError](Type1Parser("<<>>"))
  }

  test("<<Bool>>") {
    val result = Type1Parser("<<Bool>>")
    assert(TupT1(BoolT1()) == result)
  }

  test("<<Bool, Int>>") {
    val result = Type1Parser("<<Bool, Int>>")
    assert(TupT1(BoolT1(), IntT1()) == result)
  }

  test("[] is rejected") {
    assertThrows[Type1ParseError](Type1Parser("[]"))
  }

  test("[a: Int]") {
    val result = Type1Parser("[a: Int]")
    assert(RecT1(SortedMap("a" -> IntT1())) == result)
  }

  test("[a: Int, b: Bool]") {
    val result = Type1Parser("[a: Int, b: Bool]")
    assert(RecT1(SortedMap("a" -> IntT1(), "b" -> BoolT1())) == result)
  }

  test("Set(Int) -> Bool") {
    val result = Type1Parser("Set(Int) -> Bool")
    assert(FunT1(SetT1(IntT1()), BoolT1()) == result)
  }

  test("Set(Int) -> Bool -> Str") {
    val result = Type1Parser("Set(Int) -> Bool -> Str")
    assert(FunT1(SetT1(IntT1()), FunT1(BoolT1(), StrT1())) == result)
  }

  test("(Set(Int) -> Bool) -> Str") {
    val result = Type1Parser("(Set(Int) -> Bool) -> Str")
    assert(FunT1(FunT1(SetT1(IntT1()), BoolT1()), StrT1()) == result)
  }

  test("(Set(Int), Bool) => Str") {
    val result = Type1Parser("(Set(Int), Bool) => Str")
    assert(OperT1(List(SetT1(IntT1()), BoolT1()), StrT1()) == result)
  }

  test("(Set(Int) => Bool) => Str") {
    val result = Type1Parser("(Set(Int) => Bool) => Str")
    assert(OperT1(List(OperT1(List(SetT1(IntT1())), BoolT1())), StrT1()) == result)
  }

  test("(Set(Int) -> Bool) => Str") {
    val result = Type1Parser("(Set(Int) -> Bool) => Str")
    assert(OperT1(List(FunT1(SetT1(IntT1()), BoolT1())), StrT1()) == result)
  }

}