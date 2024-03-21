package at.forsyte.apalache.io.quint

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import at.forsyte.apalache.io.quint.QuintType._
import at.forsyte.apalache.tla.lir.{
  ConstT1, FunT1, IntT1, RecRowT1, RowT1, SparseTupT1, StrT1, TlaType1, TupT1, VarT1, VariantT1,
}

/**
 * Tests the conversion of quint types, represented as QuintTypes, into TlaType1
 */
@RunWith(classOf[JUnitRunner])
class TestQuintTypes extends AnyFunSuite {

  val translate: QuintType => TlaType1 = (new QuintTypeConverter).convert(_)

  test("Quint's named type variables are converted into numbered TlaType1 variables") {
    val typeVar = QuintVarT("foo")
    assert(translate(typeVar) == VarT1(0))
  }

  test("Multiple Quint named type variables are converted into sequentially numbered TlaType1 variables") {
    val polyFun = QuintFunT(QuintVarT("a"), QuintVarT("b"))
    assert(translate(polyFun) == FunT1(VarT1(0), VarT1(1)))
  }

  test("Quint tuple types are converted correctly") {
    val tuple =
      // i.e.: (int, string)
      QuintTupleT(Row.Cell(List(RecordField("0", QuintIntT()), RecordField("1", QuintStrT())), Row.Nil()))
    assert(translate(tuple) == TupT1(IntT1, StrT1))
  }

  test("empty Quint tuple types are converted to the UNIT uninterpreted type") {
    val tuple = QuintTupleT(Row.Nil())
    assert(translate(tuple) == ConstT1("UNIT"))
  }

  test("Polymorphic Quint tuples types are converted to sparse tuples") {
    val tuple =
      // i.e.: (int, string | r)
      QuintTupleT(Row.Cell(List(RecordField("0", QuintIntT()), RecordField("1", QuintStrT())), Row.Var("r")))
    assert(translate(tuple) == SparseTupT1(1 -> IntT1, 2 -> StrT1))
  }

  test("Open Quint record types are converted into open TlaType1 records") {
    val record =
      // i.e.: { f1: int, f2: string | r }
      QuintRecordT(Row.Cell(List(RecordField("f1", QuintIntT()), RecordField("f2", QuintStrT())), Row.Var("r")))
    assert(translate(record) == RecRowT1(RowT1(VarT1(0), ("f1" -> IntT1), ("f2" -> StrT1))))
  }

  test("Closed Quint record types are converted into closed TlaType1 records") {
    val record =
      // i.e.: { f1: int, f2: string }
      QuintRecordT(Row.Cell(List(RecordField("f1", QuintIntT()), RecordField("f2", QuintStrT())), Row.Nil()))
    assert(translate(record) == RecRowT1(RowT1(("f1" -> IntT1), ("f2" -> StrT1))))
  }

  test("Quint sum types are converted into TlaType1 variants") {
    val quintSumType =
      // i.e.: F1(int) | F2(str)
      QuintSumT(Row.Cell(List(RecordField("F1", QuintIntT()), RecordField("F2", QuintStrT())), Row.Nil()))

    val expectedVariant =
      // i.e.: F1(Int) | F1(Str)
      VariantT1(RowT1("F1" -> IntT1, "F2" -> StrT1))
    assert(translate(quintSumType) == expectedVariant)
  }

  // tictactoe.json is located in tla-io/src/test/resources/tictactoe.json
  test("Can convert types out of tictactoe.json") {
    val tictactoeQuintJson = scala.io.Source.fromResource("tictactoe.json").mkString
    val quintTypes = QuintOutput.read(tictactoeQuintJson).get.types
    // All type conversions go through
    quintTypes.map { case (id, t) => (id, t.typ, translate(t.typ)) }
  }
}
