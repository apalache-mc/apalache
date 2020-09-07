package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.typecheck.parser.{Type1ParseError, DefaultType1Parser}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestDefaultType1Parser  extends FunSuite {
  test("non-sense") {
    assertThrows[Type1ParseError](DefaultType1Parser("non-sense"))
  }

  test("Int") {
    val result = DefaultType1Parser("Int")
    assert(IntT1() == result)
  }

  test("Real") {
    val result = DefaultType1Parser("Real")
    assert(RealT1() == result)
  }

  test("Bool") {
    val result = DefaultType1Parser("Bool")
    assert(BoolT1() == result)
  }

  test("Str") {
    val result = DefaultType1Parser("Str")
    assert(StrT1() == result)
  }

  test("var a") {
    val result = DefaultType1Parser("a")
    assert(VarT1("a") == result)
  }

  test("const PID") {
    val result = DefaultType1Parser("PID")
    assert(ConstT1("PID") == result)
  }

  test("Set(Int)") {
    val result = DefaultType1Parser("Set(Int)")
    assert(SetT1(IntT1()) == result)
  }

  test("Seq(Int)") {
    val result = DefaultType1Parser("Seq(Int)")
    assert(SeqT1(IntT1()) == result)
  }

  test("<<>> is rejected") {
    assertThrows[Type1ParseError](DefaultType1Parser("<<>>"))
  }

  test("<<Bool>>") {
    val result = DefaultType1Parser("<<Bool>>")
    assert(TupT1(BoolT1()) == result)
  }

  test("<<Bool, Int>>") {
    val result = DefaultType1Parser("<<Bool, Int>>")
    assert(TupT1(BoolT1(), IntT1()) == result)
  }

  test("[] is rejected") {
    assertThrows[Type1ParseError](DefaultType1Parser("[]"))
  }

  test("[a: Int]") {
    val result = DefaultType1Parser("[a: Int]")
    assert(RecT1(SortedMap("a" -> IntT1())) == result)
  }

  test("[a: Int, b: Bool]") {
    val result = DefaultType1Parser("[a: Int, b: Bool]")
    assert(RecT1(SortedMap("a" -> IntT1(), "b" -> BoolT1())) == result)
  }

  test("[f1: Int, f2: Bool]") {
    val result = DefaultType1Parser("[f1: Int, f2: Bool]")
    assert(RecT1(SortedMap("f1" -> IntT1(), "f2" -> BoolT1())) == result)
  }

  test("Set(Int) -> Bool") {
    val result = DefaultType1Parser("Set(Int) -> Bool")
    assert(FunT1(SetT1(IntT1()), BoolT1()) == result)
  }

  test("Set(Int) -> Bool -> Str") {
    val result = DefaultType1Parser("Set(Int) -> Bool -> Str")
    assert(FunT1(SetT1(IntT1()), FunT1(BoolT1(), StrT1())) == result)
  }

  test("(Set(Int) -> Bool) -> Str") {
    val result = DefaultType1Parser("(Set(Int) -> Bool) -> Str")
    assert(FunT1(FunT1(SetT1(IntT1()), BoolT1()), StrT1()) == result)
  }

  test("(Set(Int), Bool) => Str") {
    val result = DefaultType1Parser("(Set(Int), Bool) => Str")
    assert(OperT1(List(SetT1(IntT1()), BoolT1()), StrT1()) == result)
  }

  test("(Set(Int) => Bool) => Str") {
    val result = DefaultType1Parser("(Set(Int) => Bool) => Str")
    assert(OperT1(List(OperT1(List(SetT1(IntT1())), BoolT1())), StrT1()) == result)
  }

  test("(Set(Int) -> Bool) => Str") {
    val result = DefaultType1Parser("(Set(Int) -> Bool) => Str")
    assert(OperT1(List(FunT1(SetT1(IntT1()), BoolT1())), StrT1()) == result)
  }

}