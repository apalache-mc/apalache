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

  test("the same free variable name bound in independent function heads do not interfere") {
    val builder = new ScopedBuilder()
    val v = builder.name("x", IntT1)
    val _1 = builder.int(1)
    val intS = builder.intSet()
    // Two independent functions of the form [x \in Int |-> 1]
    val f1 = builder.funDef(_1, (v, intS))
    val f2 = builder.funDef(_1, (v, intS))
    // We should be able to construct a two item set, including these two functions
    val setEx: TlaEx = build(builder.enumSet(f1, f2))
    assert(setEx.typeTag == Typed(SetT1(FunT1(IntT1, IntT1))))
  }

}
