package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.typecomp.pbt._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers
import org.scalacheck.Prop._
import scala.util.Try

@RunWith(classOf[JUnitRunner])
class TestRowTypedRecords extends AnyFunSuite with Checkers {

  val GenTBI = GenTBuilderInstruction

  test("can construct row-typed records") {
    implicit val builder = new ScopedBuilder()
    val prop =
      forAll(Gen.zip(GenTBI.rowVar, GenTBI.genRecordFields)) { case (rowVar, fields) =>
        build(builder.rowRec(rowVar, fields: _*)) match {
          case _ @OperEx(TlaFunOper.rec, _*) => true
          case _                             => false
        }
      }

    check(prop, minSuccessful(1000), sizeRange(4))
  }

  test("can construct application of row-polymorphic operator to two different, compatible records") {
    val builder = new ScopedBuilder()
    // [ f1 |-> 1 ]
    val a = builder.rowRec(None, "f1" -> builder.int(1))
    // [ f1 |-> 1, f2 |-> "s" ]
    val b = builder.rowRec(None, "f1" -> builder.int(2), "f2" -> builder.str("s"))
    // {f1: Int | a}
    val openRecType = RecRowT1(RowT1(VarT1(1), "f1" -> IntT1))
    // op : ({f1: Int | a}) => Int
    val opName = builder.name("op", OperT1(Seq(openRecType), IntT1))
    // << op(a), op(b) >>
    val operatorApplications =
      builder.seq(
          builder.appOp(opName, a),
          builder.appOp(opName, b),
      )

    // Regresson test for https://github.com/apalache-mc/apalache/issues/2581
    assert(Try(build(operatorApplications)).isSuccess,
        "Failed to build the application of row-polymorphic operator to compatible records")
  }
}
