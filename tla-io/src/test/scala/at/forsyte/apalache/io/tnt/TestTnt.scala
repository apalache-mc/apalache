package at.forsyte.apalache.io.tnt

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import at.forsyte.apalache.io.tnt.TntType._
import at.forsyte.apalache.tla.lir.{FunT1, IntT1, RecRowT1, RowT1, StrT1, TupT1, VarT1, VariantT1}

@RunWith(classOf[JUnitRunner])
class TestTnt extends AnyFunSuite {

  test("TNT's named type variables are converted into numbered TlaType1 variables") {
    val typeVar = TntVarT("foo")
    assert(Tnt.typeToTlaType(typeVar) == VarT1(0))
  }

  test("Multiple TNT named type variables are converted into sequentially numbered TlaType1 variables") {
    val polyFun = TntFunT(TntVarT("a"), TntVarT("b"))
    assert(Tnt.typeToTlaType(polyFun) == FunT1(VarT1(0), VarT1(1)))
  }

  test("TNT tuple types are converted correctly") {
    val tuple =
      // i.e.: (int, string)
      TntTupleT(Row.Cell(List(RecordField("1", TntIntT()), RecordField("2", TntStrT())), Row.Nil()))
    assert(Tnt.typeToTlaType(tuple) == TupT1(IntT1, StrT1))
  }

  test("Polymorphic TNT tuples types are converted to plain, closed tuples") {
    val tuple =
      // i.e.: (int, string | r)
      TntTupleT(Row.Cell(List(RecordField("1", TntIntT()), RecordField("2", TntStrT())), Row.Var("r")))
    assert(Tnt.typeToTlaType(tuple) == TupT1(IntT1, StrT1))
  }

  test("Open TNT record types are converted into open TlaType1 records") {
    val record =
      // i.e.: {f1: int, f2: string | r)
      TntRecordT(Row.Cell(List(RecordField("f1", TntIntT()), RecordField("f2", TntStrT())), Row.Var("r")))
    assert(Tnt.typeToTlaType(record) == RecRowT1(RowT1(VarT1(0), ("f1" -> IntT1), ("f2" -> StrT1))))
  }

  test("Closed TNT record types are converted into closed TlType1 records") {
    val record =
      // i.e.: {f1: int, f2: string)
      TntRecordT(Row.Cell(List(RecordField("f1", TntIntT()), RecordField("f2", TntStrT())), Row.Nil()))
    assert(Tnt.typeToTlaType(record) == RecRowT1(RowT1(("f1" -> IntT1), ("f2" -> StrT1))))
  }

  test("TNT unions are converted int TlaType1 variants") {
    val opt1 =
      // i.e.: {tag: "t1", f1: int}
      UnionRecord("t1", Row.Cell(List(RecordField("f1", TntIntT())), Row.Nil()))
    val opt2 =
      // i.e.: {tag: "t2", f2: string}
      UnionRecord("t2", Row.Cell(List(RecordField("f2", TntStrT())), Row.Nil()))
    val variant =
      // i.e.: | {tag: "t1", f1: int} | {tag: "t2", f2: string}
      TntUnionT("tag", List(opt1, opt2))

    val expectedVariant =
      // i.e.: t1({ f1: Int }) | t2({ f2: Str })
      VariantT1(RowT1("t1" -> RecRowT1(RowT1(("f1" -> IntT1))), "t2" -> RecRowT1(RowT1(("f2" -> StrT1)))))
    assert(Tnt.typeToTlaType(variant) == expectedVariant)
  }

  // tictactoe.json is located in tla-io/src/test/resources/tictactoe.json
  test("Can convert types out of tictactoe.json") {
    val tictactoeTntJson = scala.io.Source.fromResource("tictactoe.json").mkString
    val tntTypes = TntcOutput.read(tictactoeTntJson).get.types
    // All type conversions go through
    tntTypes.map { case (id, t) => (id, t.typ, Tnt.typeToTlaType(t.typ)) }
  }
}
