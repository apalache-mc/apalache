package at.forsyte.apalache.tla.lir

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestTlaType1 extends AnyFunSuite {
  test("TlaType1.toString") {
    // Type System 1
    assert("Int" == IntT1().toString)
    assert("Real" == RealT1().toString)
    assert("Bool" == BoolT1().toString)
    assert("Str" == StrT1().toString)
    assert("PID" == ConstT1("PID").toString)
    assert("a" == VarT1(0).toString)
    assert("a" == VarT1("a").toString)
    assert("z" == VarT1("z").toString)
    assert("z" == VarT1(25).toString)
    assert("Set(a)" == SetT1(VarT1("a")).toString)
    assert("Set(Int)" == SetT1(IntT1()).toString)
    assert("Seq(a)" == SeqT1(VarT1("a")).toString)
    assert("Seq(Int)" == SeqT1(IntT1()).toString)
    assert("(Int -> Bool)" == FunT1(IntT1(), BoolT1()).toString)
    assert("<<Int, Bool, Str>>" == TupT1(IntT1(), BoolT1(), StrT1()).toString)
    val recType = RecT1(SortedMap("f1" -> IntT1(), "f2" -> BoolT1(), "f3" -> StrT1()))
    assert("[f1: Int, f2: Bool, f3: Str]" == recType.toString)
    val operType = OperT1(List(BoolT1(), StrT1()), IntT1())
    assert("((Bool, Str) => Int)" == operType.toString)
  }

  test("TlaType1.toString of ADR014") {
    // ADR014 extensions
    assert("." == RowNilT1().toString)
    // generic syntax for rows
    assert("# f: Int | z #" == RowConsT1("f", IntT1(), VarT1("z")).toString)
    assert("# f: Int | . #" == RowConsT1("f", IntT1(), RowNilT1()).toString)
    assert("# g: Bool | # f: Int | z # #" == RowConsT1("g", BoolT1(), RowConsT1("f", IntT1(), VarT1("z"))).toString)
    // generic syntax for the records that exposes rows (since z is a variable)
    assert("{ # f: Int | z # }" == RecRowT1(RowConsT1("f", IntT1(), VarT1("z"))).toString)
    // special user friendly syntax for the records (since there are no variables in the rows)
    assert("{ f: Int, g: a }" == RecRowT1(RowConsT1("f", IntT1(), RowConsT1("g", VarT1("a"), RowNilT1()))).toString)
    // generic syntax for the variants that exposes rows (since z is a variable)
    val recRow1 = RecRowT1(RowConsT1("tag", StrT1(), RowConsT1("f", IntT1(), RowNilT1())))
    assert("/ # tag1: { tag: Str, f: Int } | z # /" == VariantT1(RowConsT1("tag1", recRow1, VarT1("z"))).toString)
    val recRow2 = RecRowT1(RowConsT1("tag", StrT1(), RowConsT1("g", BoolT1(), RowNilT1())))
    assert("/ # tag2: { tag: Str, g: Bool } | # tag1: { tag: Str, f: Int } | z # # /"
      == VariantT1(RowConsT1("tag2", recRow2, RowConsT1("tag1", recRow1, VarT1("z")))).toString)
    // special user friendly syntax for the variants (since there are no variables in the rows)
    assert("""/ tag1: { tag: Str, f: Int } | tag2: { tag: Str, g: Bool } /"""
      == VariantT1(RowConsT1("tag1", recRow1, RowConsT1("tag2", recRow2, RowNilT1()))).toString)
  }
}
