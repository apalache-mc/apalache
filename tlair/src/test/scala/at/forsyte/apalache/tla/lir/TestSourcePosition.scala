package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.src.SourcePosition
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSourcePosition extends AnyFunSuite {
  val pos0 = SourcePosition(0, 0)
  val pos1 = SourcePosition(15, 20)
  val pos2 = SourcePosition(15, 20)
  val pos3 = SourcePosition(15, 55)
  val pos4 = SourcePosition(19, 5)
  val pos5 = SourcePosition(19, 20)
  val pos6 = SourcePosition(5454, 4646)

  test("toString") {
    assert(pos0.toString == "0:0")
    assert(pos1.toString == "15:20")
    assert(pos2.toString == "15:20")
    assert(pos3.toString == "15:55")
    assert(pos4.toString == "19:5")
    assert(pos5.toString == "19:20")
    assert(pos6.toString == "5454:4646")
  }

  test("equals") {
    // equal line and column
    assert(pos1 == pos2)
    assert(pos2 == pos1)

    // different line and column
    assert(pos0 != pos1)
    assert(pos0 != pos2)
    assert(pos0 != pos3)
    assert(pos0 != pos4)
    assert(pos0 != pos5)
    assert(pos0 != pos6)

    // different line, same column
    assert(pos1 != pos5)

    // same line, different column
    assert(pos2 != pos3)
  }

  test("equals have same hashCode") {
    assert(pos1.hashCode() == pos2.hashCode())
    assert(pos6.hashCode() == SourcePosition(5454, 4646).hashCode())
  }
}
