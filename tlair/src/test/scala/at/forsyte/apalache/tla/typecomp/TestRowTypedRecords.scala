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

@RunWith(classOf[JUnitRunner])
class TestRowTypedRecords extends AnyFunSuite with Checkers {

  val GenTBI = TypecompPBT.GenTBuilderInstruction

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

}
