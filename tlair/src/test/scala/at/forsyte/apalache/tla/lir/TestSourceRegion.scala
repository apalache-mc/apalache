package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.src.{SourcePosition, SourceRegion}
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSourceRegion extends AnyFunSuite {
  val pos0 = SourcePosition(0, 0)
  val pos1 = SourcePosition(15, 20)
  val pos2 = SourcePosition(15, 20)
  val pos3 = SourcePosition(15, 55)
  val pos4 = SourcePosition(19, 5)
  val pos5 = SourcePosition(19, 20)
  val pos6 = SourcePosition(5454, 4646)

  val root = SourceRegion(pos0, pos6)
  val r15 = SourceRegion(pos1, pos5)
  val r16 = SourceRegion(pos1, pos6)
  val r24 = SourceRegion(pos2, pos4)
  val r04 = SourceRegion(pos0, pos4)
  val r01 = SourceRegion(pos0, pos1)
  val r56 = SourceRegion(pos5, pos6)

  test("toString") {
    assert(root.toString == "0:0-5454:4646")
    assert(r15.toString == "15:20-19:20")
    assert(r24.toString == "15:20-19:5")
    assert(r04.toString == "0:0-19:5")
  }

  test("equals") {
    assert(root == SourceRegion(0, 0, 5454, 4646))
    assert(root == SourceRegion(pos0, pos6))

    assert(root != r15)
    assert(root != r24)
    assert(root != r04)
    assert(r15 != r24)
    assert(r15 != r04)
    assert(r24 != r04)
  }

  test("equals have same hashCode") {
    assert(root.hashCode() == SourceRegion(0, 0, 5454, 4646).hashCode())
    assert(root.hashCode() == SourceRegion(pos0, pos6).hashCode())
    assert(r24.hashCode() == SourceRegion(pos2, pos4).hashCode())
  }

  test("compare") {
    Seq(pos1, pos2, pos3, pos4, pos5, pos6).foreach(p => assert(p > pos0))
    assert(pos1.compare(pos2) == 0)
    Seq(pos0, pos1, pos2, pos3, pos4, pos5).foreach(p => assert(p < pos6))
    assert(pos2.compare(pos3) < 0)
  }

  test("isInside") {
    assert(r15.isInside(root))
    assert(r16.isInside(root))
    assert(r24.isInside(root))
    assert(r04.isInside(root))

    assert(!root.isInside(r15))
    assert(!root.isInside(r16))
    assert(!root.isInside(r24))
    assert(!root.isInside(r04))

    assert(r15.isInside(r16))
    assert(r24.isInside(r16))
  }

  test("contains") {
    assert(root.contains(r15))
    assert(root.contains(r16))
    assert(root.contains(r24))
    assert(root.contains(r04))

    assert(!r15.contains(root))
    assert(!r16.contains(root))
    assert(!r24.contains(root))
    assert(!r04.contains(root))

    assert(!r15.contains(r16))
    assert(!r24.contains(r16))
  }

  test("isIntersecting") {
    // inclusion
    assert(root.isIntersecting(r15))
    assert(root.isIntersecting(r16))
    assert(root.isIntersecting(r24))
    assert(root.isIntersecting(r04))

    // membership
    assert(r15.isIntersecting(root))
    assert(r16.isIntersecting(root))
    assert(r24.isIntersecting(root))
    assert(r04.isIntersecting(root))

    // non-trivial intersection
    assert(r15.isIntersecting(r16))
    assert(r15.isIntersecting(r24))
    assert(r15.isIntersecting(r04))

    // shared boundary
    assert(r01.isIntersecting(r15))
    assert(r01.isIntersecting(r16))
    assert(r15.isIntersecting(r01))
    assert(r16.isIntersecting(r01))

    // disjoint
    assert(!r01.isIntersecting(r56))
  }
}
