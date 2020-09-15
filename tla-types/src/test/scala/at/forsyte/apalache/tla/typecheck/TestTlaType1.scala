package at.forsyte.apalache.tla.typecheck

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestTlaType1  extends FunSuite {
  test("TlaType1.toString") {
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
    assert("(Bool, Str) => Int" == operType.toString)
  }
}