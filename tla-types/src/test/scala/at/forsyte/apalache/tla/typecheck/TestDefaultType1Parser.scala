package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.io.typecheck.parser.Type1ParseError
import at.forsyte.apalache.tla.lir.{
  BoolT1, ConstT1, FunT1, IntT1, OperT1, RealT1, RecRowT1, RecT1, RowT1, SeqT1, SetT1, SparseTupT1, StrT1, TlaType1Gen,
  TupT1, VarT1, VariantT1,
}
import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import org.junit.runner.RunWith
import org.scalacheck.Gen.alphaStr
import org.scalacheck.Prop
import org.scalacheck.Prop.{falsified, forAll, passed, AnyOperators}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestDefaultType1Parser extends AnyFunSuite with Checkers with TlaType1Gen {

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

  test("<| 3: Bool, 5: Int |>") {
    val result = DefaultType1Parser("<| 3: Bool, 5: Int |>")
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

  test("one-line comments") {
    val text =
      """
        |Set([
        |  // this comment explains something about tags
        |  tag: Str,
        |  // this comment explains something about values
        |  value: Int
        |])
        |""".stripMargin
    val result = DefaultType1Parser.parseType(text)
    assert(SetT1(RecT1("tag" -> StrT1(), "value" -> IntT1())) == result)
  }

  // ADR014: rows, new records, and variants
  test("empty row") {
    val text = """(||)"""
    val result = DefaultType1Parser.parseType(text)
    assert(RowT1() == result)
  }

  test("concrete row") {
    val text = """(| f: Int | g: c |)"""
    val result = DefaultType1Parser.parseType(text)
    assert(RowT1("f" -> IntT1(), "g" -> VarT1("c")) == result)
  }

  test("parametric row") {
    val text = """(| f: Int | g: Bool | x |)"""
    val result = DefaultType1Parser.parseType(text)
    assert(RowT1(VarT1("x"), "f" -> IntT1(), "g" -> BoolT1()) == result)
  }

  test("empty row record") {
    val text = """{ }"""
    val result = DefaultType1Parser.parseType(text)
    assert(RecRowT1(RowT1()) == result)
  }

  test("unknown record") {
    // The only thing we know is that it is a record.
    // Type variable 'a' should be a parametric row.
    val text = """{ a }"""
    val result = DefaultType1Parser.parseType(text)
    assert(RecRowT1(RowT1(VarT1("a"))) == result)
  }

  test("record from a row") {
    val text = """{ f: Int, g: a }"""
    val result = DefaultType1Parser.parseType(text)
    assert(RecRowT1(RowT1("f" -> IntT1(), "g" -> VarT1("a"))) == result)
  }

  test("record from a row with a parametric tail") {
    val text = """{ f: Int, g: a, x }"""
    val result = DefaultType1Parser.parseType(text)
    assert(RecRowT1(RowT1(VarT1("x"), "f" -> IntT1(), "g" -> VarT1("a"))) == result)
  }

  test("a record with duplicate keys should throw") {
    val text = """{ f: Int, f: Bool }"""
    assertThrows[Type1ParseError] {
      DefaultType1Parser.parseType(text)
    }
  }

  test("empty variant") {
    // special syntax for an empty variant
    val text = "Variant()"
    val result = DefaultType1Parser.parseType(text)
    assert(VariantT1(RowT1()) == result)
  }

  test("unknown variant") {
    // special syntax for a variant that is completely parametric
    val text = "Variant(a)"
    val result = DefaultType1Parser.parseType(text)
    assert(VariantT1(RowT1(VarT1("a"))) == result)
  }

  test("variant from rows") {
    val text = """{ tag: "tag1", f: Int } | { tag: "tag2", g: Bool, c }"""
    val result = DefaultType1Parser.parseType(text)
    val row1 = RecRowT1(RowT1("tag" -> StrT1(), "f" -> IntT1()))
    val row2 = RecRowT1(RowT1(VarT1("c"), "tag" -> StrT1(), "g" -> BoolT1()))
    assert(VariantT1(RowT1("tag1" -> row1, "tag2" -> row2)) == result)
  }

  test("variant with duplicate tag should throw") {
    val text = """{ tag: "tag1", f: Int, tag: "tag2" } | c"""
    assertThrows[Type1ParseError] {
      DefaultType1Parser.parseType(text)
    }
  }

  test("variant with duplicate fields should throw") {
    val text = """{ tag: "tag1", f: Int, f: Bool } | c"""
    assertThrows[Type1ParseError] {
      DefaultType1Parser.parseType(text)
    }
  }

  test("variant from rows with a parametric tail") {
    val text = """{ tag: "tag1", f: Int } | { tag: "tag2", g: Bool } | c"""
    val result = DefaultType1Parser.parseType(text)
    val row1 = RecRowT1(RowT1("tag" -> StrT1(), "f" -> IntT1()))
    val row2 = RecRowT1(RowT1("tag" -> StrT1(), "g" -> BoolT1()))
    assert(VariantT1(RowT1(VarT1("c"), "tag1" -> row1, "tag2" -> row2)) == result)
  }

  test("variant with duplicate tags should throw") {
    val text = """{ tag: "tag1", f: Int } | { tag: "tag1", g: Bool } | c"""
    assertThrows[Type1ParseError] {
      DefaultType1Parser.parseType(text)
    }
  }

  test("a set over a variant") {
    val text =
      """
        | Set({ tag: "req", ask: Int } | { tag: "ack", success: Bool })
        |""".stripMargin
    val result = DefaultType1Parser.parseType(text)
    val row1 = RecRowT1(RowT1("tag" -> StrT1(), "ask" -> IntT1()))
    val row2 = RecRowT1(RowT1("tag" -> StrT1(), "success" -> BoolT1()))
    assert(SetT1(VariantT1(RowT1("req" -> row1, "ack" -> row2))) == result)
  }

  test("variant constructor") {
    // a type that we could use in Variant!Variant, if we knew "$tagValue"
    val text =
      """
        | { tag: Str, a } =>
        |     { tag: "$tagValue", a } | b
        |""".stripMargin
    val result = DefaultType1Parser.parseType(text)
    val rec = RecRowT1(RowT1(VarT1("a"), "tag" -> StrT1()))
    val variant = VariantT1(RowT1(VarT1("b"), "$tagValue" -> rec))
    assert(OperT1(Seq(rec), variant) == result)
  }

  test("filter over variant set") {
    // a type that we could use in Variant!FilterByTag, if we knew "$tagValue"
    val text =
      """
        |  (Set({ tag: "$tagValue", a} | b), Str) => Set({ tag: Str, a })
        |""".stripMargin
    val result = DefaultType1Parser.parseType(text)
    val rec = RecRowT1(RowT1(VarT1("a"), "tag" -> StrT1()))
    val variant = VariantT1(RowT1(VarT1("b"), "$tagValue" -> rec))
    assert(OperT1(Seq(SetT1(variant), StrT1()), SetT1(rec)) == result)
  }

  test("match a singleton variant") {
    // a type that we could use in Variant!MatchOnly, if we knew "$tagValue"
    val text =
      """
        | (
        |   { tag: "$tagValue", a },
        |   { tag: Str, a } => r
        | ) => r
        |""".stripMargin
    val result = DefaultType1Parser.parseType(text)
    val rec = RecRowT1(RowT1(VarT1("a"), "tag" -> StrT1()))
    val variant = VariantT1(RowT1("$tagValue" -> rec))
    assert(OperT1(Seq(variant, OperT1(Seq(rec), VarT1("r"))), VarT1("r")) == result)
  }

  test("match a variant by tag") {
    // a type that we could use in Variant!MatchTag, if we knew "$tagValue"
    val text =
      """
        | (
        |   { tag: "$tagValue", a } | b,
        |   { tag: Str, a } => r,
        |   Variant(b) => r
        | ) => r
        |""".stripMargin
    val result = DefaultType1Parser.parseType(text)
    val rec = RecRowT1(RowT1(VarT1("a"), "tag" -> StrT1()))
    val variant = VariantT1(RowT1(VarT1("b"), "$tagValue" -> rec))
    val thenOper = OperT1(Seq(rec), VarT1("r"))
    val elseOper = OperT1(Seq(VariantT1(RowT1(VarT1("b")))), VarT1("r"))
    assert(OperT1(Seq(variant, thenOper, elseOper), VarT1("r")) == result)
  }

  // property-based tests

  test("no crashes: either parse, or raise an error") {
    check({
          forAll(alphaStr) { str =>
            try {
              DefaultType1Parser(str)
              passed
            } catch {
              case _: Type1ParseError =>
                passed

              case _: Throwable =>
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

    check(recursiveTypesParse, minSuccessful(1000), sizeRange(7))
  }
}
