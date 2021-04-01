package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{
  BoolT1, ConstT1, FunT1, IntT1, OperT1, RealT1, RecT1, SeqT1, SetT1, SparseTupT1, StrT1, TupT1, VarT1
}
import at.forsyte.apalache.tla.typecheck.parser.{DefaultType1Parser, Type1ParseError}
import org.junit.runner.RunWith
import org.scalacheck.Gen.alphaStr
import org.scalacheck.Prop
import org.scalacheck.Prop.{AnyOperators, falsified, forAll, passed}
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestDefaultType1Parser extends FunSuite with Checkers with TlaType1Gen {

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

  test("{ 3: Bool, 5: Int }") {
    val result = DefaultType1Parser("{ 3: Bool, 5: Int }")
    assert(SparseTupT1(SortedMap(3 -> BoolT1(), 5 -> IntT1())) == result)
  }

  test("[] is ok") {
    val result = DefaultType1Parser("[]")
    assert(RecT1() == result)
  }

  test("[a: Int]") {
    val result = DefaultType1Parser("[a: Int]")
    assert(RecT1(SortedMap("a" -> IntT1())) == result)
  }

  test("[a: Int, b: Bool]") {
    val result = DefaultType1Parser("[a: Int, b: Bool]")
    assert(RecT1(SortedMap("a" -> IntT1(), "b" -> BoolT1())) == result)
  }

  test("multiline [a: Int, b: Bool]") {
    val text =
      """
        |[a: Int,
        | b: Bool]
        |""".stripMargin
    val result = DefaultType1Parser(text)
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

  test("(Set(Int) -> Bool)") {
    val result = DefaultType1Parser("(Set(Int) -> Bool)")
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

  test("((Set(Int), Bool) => Str)") {
    val result = DefaultType1Parser("((Set(Int), Bool) => Str)")
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

  test("vc") {
    // found by scalacheck
    assertThrows[Type1ParseError](DefaultType1Parser("vc"))
  }

  test("ALIAS1 = Int") {
    val (name, tt) = DefaultType1Parser.parseAlias("ALIAS1 = [a: Int, b: Bool]")
    assert("ALIAS1" == name)
    assert(RecT1("a" -> IntT1(), "b" -> BoolT1()) == tt)
  }

  test("ALIAS2 = Set(ALIAS1)") {
    val (name, tt) = DefaultType1Parser.parseAlias("ALIAS2 = Set(ALIAS1)")
    assert("ALIAS2" == name)
    // ALIAS1 is not replaced immediately, it has to be substituted when we have the map of all aliases
    assert(SetT1(ConstT1("ALIAS1")) == tt)
  }

  test("incorrect name: alias1 = Set(ALIAS3)") {
    assertThrows[Type1ParseError](DefaultType1Parser.parseAlias("alias1 = Set(ALIAS3)"))
  }

  test("Set(ENTRY)") {
    val result = DefaultType1Parser.parseType("Set(ENTRY)")
    assert(SetT1(ConstT1("ENTRY")) == result)
  }

  test("no crashes: either parse, or raise an error") {
    check({
      forAll(alphaStr) { str =>
        try {
          DefaultType1Parser(str)
          passed
        } catch {
          case _: Type1ParseError =>
            passed

          case _ =>
            falsified
        }
      // no exceptions
      }
    }, minSuccessful(300))
  }

  test("parse primitive types") {
    def primitivesParse: Prop = {
      forAll(genPrimitive) { primitive =>
        DefaultType1Parser(primitive.toString) ?= primitive
      }
    }

    check(primitivesParse, minSuccessful(300))
  }

  test("parse recursive types") {
    def recursiveTypesParse: Prop = {
      forAll(genType1) { typ =>
        DefaultType1Parser(typ.toString) ?= typ
      }
    }

    check(recursiveTypesParse, minSuccessful(10000), sizeRange(7))
  }
}
