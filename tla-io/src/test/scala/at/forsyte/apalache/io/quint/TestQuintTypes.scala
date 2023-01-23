package at.forsyte.apalache.io.quint

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import at.forsyte.apalache.io.quint.QuintType._
import at.forsyte.apalache.tla.lir.{FunT1, IntT1, RecRowT1, RowT1, StrT1, TupT1, VarT1, VariantT1}

/**
 * Tests the conversion of quint types, represented as QuintTypes, into TlaType1
 */
@RunWith(classOf[JUnitRunner])
class TestQuintTypes extends AnyFunSuite {

  test("Quint's named type variables are converted into numbered TlaType1 variables") {
    val typeVar = QuintVarT("foo")
    assert(Quint.typeToTlaType(typeVar) == VarT1(0))
  }

  test("Multiple Quint named type variables are converted into sequentially numbered TlaType1 variables") {
    val polyFun = QuintFunT(QuintVarT("a"), QuintVarT("b"))
    assert(Quint.typeToTlaType(polyFun) == FunT1(VarT1(0), VarT1(1)))
  }

  test("Quint tuple types are converted correctly") {
    val tuple =
      // i.e.: (int, string)
      QuintTupleT(Row.Cell(List(RecordField("1", QuintIntT()), RecordField("2", QuintStrT())), Row.Nil()))
    assert(Quint.typeToTlaType(tuple) == TupT1(IntT1, StrT1))
  }

  test("Polymorphic Quint tuples types are converted to plain, closed tuples") {
    val tuple =
      // i.e.: (int, string | r)
      QuintTupleT(Row.Cell(List(RecordField("1", QuintIntT()), RecordField("2", QuintStrT())), Row.Var("r")))
    assert(Quint.typeToTlaType(tuple) == TupT1(IntT1, StrT1))
  }

  test("Open Quint record types are converted into open TlaType1 records") {
    val record =
      // i.e.: { f1: int, f2: string | r }
      QuintRecordT(Row.Cell(List(RecordField("f1", QuintIntT()), RecordField("f2", QuintStrT())), Row.Var("r")))
    assert(Quint.typeToTlaType(record) == RecRowT1(RowT1(VarT1(0), ("f1" -> IntT1), ("f2" -> StrT1))))
  }

  test("Closed Quint record types are converted into closed TlaType1 records") {
    val record =
      // i.e.: { f1: int, f2: string }
      QuintRecordT(Row.Cell(List(RecordField("f1", QuintIntT()), RecordField("f2", QuintStrT())), Row.Nil()))
    assert(Quint.typeToTlaType(record) == RecRowT1(RowT1(("f1" -> IntT1), ("f2" -> StrT1))))
  }

  test("Quint unions are converted into TlaType1 variants") {
    val opt1 =
      // i.e.: {tag: "t1", f1: int}
      UnionRecord("t1", Row.Cell(List(RecordField("f1", QuintIntT())), Row.Nil()))
    val opt2 =
      // i.e.: {tag: "t2", f2: string}
      UnionRecord("t2", Row.Cell(List(RecordField("f2", QuintStrT())), Row.Nil()))
    val variant =
      // i.e.: | {tag: "t1", f1: int} | {tag: "t2", f2: string}
      QuintUnionT("tag", List(opt1, opt2))

    val expectedVariant =
      // i.e.: t1({ f1: Int }) | t2({ f2: Str })
      VariantT1(RowT1("t1" -> RecRowT1(RowT1(("f1" -> IntT1))), "t2" -> RecRowT1(RowT1(("f2" -> StrT1)))))
    assert(Quint.typeToTlaType(variant) == expectedVariant)
  }

  // tictactoe.json is located in tla-io/src/test/resources/tictactoe.json
  test("Can convert types out of tictactoe.json") {
    val tictactoeQuintJson = scala.io.Source.fromResource("tictactoe.json").mkString
    val quintTypes = QuintOutput.read(tictactoeQuintJson).get.types
    // All type conversions go through
    quintTypes.map { case (id, t) => (id, t.typ, Quint.typeToTlaType(t.typ)) }
  }
}
