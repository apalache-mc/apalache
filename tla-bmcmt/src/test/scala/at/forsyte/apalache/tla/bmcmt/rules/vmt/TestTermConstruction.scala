package at.forsyte.apalache.tla.bmcmt.rules.vmt

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.formulas.EUF._
import at.forsyte.apalache.tla.lir.formulas.Integers.{IntLiteral, IntVar}
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas._

@RunWith(classOf[JUnitRunner])
class TestTermConstruction extends AnyFunSuite {

  val int1: Term = IntLiteral(1)
  val int2: Term = IntLiteral(2)
  val intV1: Term = IntVar("a")
  val intV2: Term = IntVar("b")

  val usort1: UninterpretedSort = UninterpretedSort("A")
  val usort2: UninterpretedSort = UninterpretedSort("B")

  val uval1: Term = UninterpretedLiteral("x", usort1)
  val uval2: Term = UninterpretedLiteral("y", usort2)

  val uvar1: Term = UninterpretedVar("c", usort1)
  val uvar2: Term = UninterpretedVar("d", usort2)

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

    val fNullary = FunctionSort(IntSort)
    val fUnary1 = FunctionSort(IntSort, BoolSort)
    val fUnary2 = FunctionSort(usort1, usort2)
    val fNary1 = FunctionSort(usort2, IntSort, IntSort, BoolSort)

    val fnTermNullary = FunctionVar("f", fNullary)
    val fnTermUnary1 = FunctionVar("f", fUnary1)
    val fnTermUnary2 = FunctionVar("f", fUnary2)
    val fnTermNary = FunctionVar("f", fNary1)

    // Does not throw
    Apply(fnTermNullary)
    Apply(fnTermUnary1, True)
    Apply(fnTermUnary1, BoolVar("x"))
    Equal(Apply(fnTermUnary2, uval2), uvar1)
    Apply(fnTermNary, int1, intV2, False)

    assertThrows[IllegalArgumentException] {
      Apply(fnTermUnary1, intV1)
    }

    assertThrows[IllegalArgumentException] {
      Apply(fnTermUnary2, uvar1)
    }

    assertThrows[IllegalArgumentException] {
      Apply(fnTermNary, False, uval1, intV1)
    }

  }

}
