package at.forsyte.apalache.tla.lir

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestTlaType1 extends AnyFunSuite {
  test("TlaType1.toString") {
    // Type System 1
    assert("Int" == IntT1.toString)
    assert("Real" == RealT1.toString)
    assert("Bool" == BoolT1.toString)
    assert("Str" == StrT1.toString)
    assert("PID" == ConstT1("PID").toString)
    assert("a" == VarT1(0).toString)
    assert("a" == VarT1("a").toString)
    assert("z" == VarT1("z").toString)
    assert("z" == VarT1(25).toString)
    assert("Set(a)" == SetT1(VarT1("a")).toString)
    assert("Set(Int)" == SetT1(IntT1).toString)
    assert("Seq(a)" == SeqT1(VarT1("a")).toString)
    assert("Seq(Int)" == SeqT1(IntT1).toString)
    assert("(Int -> Bool)" == FunT1(IntT1, BoolT1).toString)
    assert("<<Int, Bool, Str>>" == TupT1(IntT1, BoolT1, StrT1).toString)
    val recType = RecT1(SortedMap("f1" -> IntT1, "f2" -> BoolT1, "f3" -> StrT1))
    assert("[f1: Int, f2: Bool, f3: Str]" == recType.toString)
    val operType = OperT1(List(BoolT1, StrT1), IntT1)
    assert("((Bool, Str) => Int)" == operType.toString)
  }

  test("TlaType1.toString of ADR014 extensions") {
    // ADR014 extensions.
    // Generic syntax for rows, which is internal to the type checker and should not propagate to the user
    assert("(||)" == RowT1().toString)
    assert("(| f: Int | z |)" == RowT1(VarT1("z"), "f" -> IntT1).toString)
    assert("(| f: Int |)" == RowT1("f" -> IntT1).toString)
    assert("(| f: Int | g: Bool | z |)" == RowT1(VarT1("z"), "g" -> BoolT1, "f" -> IntT1).toString)
    // user-friendly syntax for the records, partially defined or fully defined
    assert("{ f: Int, z }" == RecRowT1(RowT1(VarT1("z"), "f" -> IntT1)).toString)
    assert("{ f: Int, g: a }" == RecRowT1(RowT1("f" -> IntT1, "g" -> VarT1("a"))).toString)
    // user-friendly syntax for the variants, partially defined or fully defined
    val recRow1 = RecRowT1(RowT1("f" -> IntT1))
    val result1 = VariantT1(RowT1(VarT1("z"), "tag1" -> recRow1)).toString
    assert("tag1({ f: Int }) | z" == result1)
    val recRow2 = RecRowT1(RowT1("g" -> BoolT1))
    val result2 = VariantT1(RowT1(VarT1("z"), "tag2" -> recRow2, "tag1" -> recRow1)).toString
    assert("tag1({ f: Int }) | tag2({ g: Bool }) | z" == result2)
    val result3 = VariantT1(RowT1("tag1" -> recRow1, "tag2" -> recRow2)).toString
    assert("tag1({ f: Int }) | tag2({ g: Bool })" == result3)
  }
}
