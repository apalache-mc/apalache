package at.forsyte.apalache.tla.bmcmt.rules.vmt

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.formulas.EUF._
import at.forsyte.apalache.tla.lir.formulas.Integers.{IntLiteral, IntVar}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.{BoolSort, IntSort, UninterpretedSort}
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas._

@RunWith(classOf[JUnitRunner])
class TestTermConstruction extends FunSuite {

  val int1 = IntLiteral(1)
  val int2 = IntLiteral(2)
  val intV1 = IntVar("a")
  val intV2 = IntVar("b")

  val usort1 = UninterpretedSort("A")
  val usort2 = UninterpretedSort("B")

  val uval1 = UninterpretedLiteral("x", usort1)
  val uval2 = UninterpretedLiteral("y", usort2)

  val uvar1 = UninterpretedVar("c", usort1)
  val uvar2 = UninterpretedVar("d", usort2)

  test("Equal requirements") {
    // Does not throw:
    Equal(int1, int2)
    Equal(uval1, uval1)
    Equal(int1, intV1)
    Equal(uvar1, uval1)

    assertThrows[IllegalArgumentException] {
      Equal(int1, uval1)
    }

    assertThrows[IllegalArgumentException] {
      Equal(uval1, uval2)
    }

  }

  test("ITE requirements") {
    // Does not throw:
    ITE(True, int1, intV2)
    ITE(False, uval2, uval2)
    ITE(Equal(int1, int2), uval1, uvar1)
    ITE(And(True, False, BoolVar("x")), True, False)

    assertThrows[IllegalArgumentException] {
      ITE(True, int1, uval1)
    }

    assertThrows[IllegalArgumentException] {
      ITE(True, uval1, uvar2)
    }

  }

  test("Apply requirements.") {

    val fNullary = Function("f", IntSort())
    val fUnary1 = Function("f", IntSort(), BoolSort())
    val fUnary2 = Function("f", usort1, usort2)
    val fNary1 = Function("f", usort2, IntSort(), IntSort(), BoolSort())

    // Does not throw
    Apply(fNullary)
    Apply(fUnary1, True)
    Apply(fUnary1, BoolVar("x"))
    Equal(Apply(fUnary2, uval2), uvar1)
    Apply(fNary1, int1, intV2, False)

    assertThrows[IllegalArgumentException] {
      Apply(fUnary1, intV1)
    }

    assertThrows[IllegalArgumentException] {
      Apply(fUnary2, uvar1)
    }

    assertThrows[IllegalArgumentException] {
      Apply(fNary1, False, uval1, intV1)
    }

  }

}
