package at.forsyte.apalache.tla.ir

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
 * Tests for LocRange
 *
 * @see at.forsyte.apalache.tlair.LocRange
 *
 * @author konnov
 */
@RunWith(classOf[JUnitRunner])
class TestLocRangeSuite extends FunSuite {
  test("1:2-3:4 is before 3:5-4:6") {
    assert(LocRange(Loc(1, 2), Loc(3, 4)) before LocRange(Loc(3, 5), Loc(4, 6)))
  }

  test("1:2-3:4 is before 4:1-4:6") {
    assert(LocRange(Loc(1, 2), Loc(3, 4)) before LocRange(Loc(4, 1), Loc(4, 6)))
  }

  test("4:1-4:6 is not before 1:2-3:4") {
    assert(!(LocRange(Loc(4, 1), Loc(4, 6)) before LocRange(Loc(1, 2), Loc(3, 4))))
  }

  test("1:2-4:2 is not before 4:1-4:6") {
    assert(!(LocRange(Loc(1, 2), Loc(4, 2)) before LocRange(Loc(4, 1), Loc(4, 6))))
  }

  test("3:5-4:6 is after 1:2-3:4") {
    assert(LocRange(Loc(3, 5), Loc(4, 6)) after LocRange(Loc(1, 2), Loc(3, 4)))
  }

  test("4:1-4:6 is after 1:2-3:4") {
    assert(LocRange(Loc(4, 1), Loc(4, 6)) after LocRange(Loc(1, 2), Loc(3, 4)))
  }

  test("1:2-3:4 is not after 4:1-4:6") {
    assert(!(LocRange(Loc(1, 2), Loc(3, 4)) after LocRange(Loc(4, 1), Loc(4, 6))))
  }

  test("4:1-4:6 is not after 1:2-4:2") {
    assert(!(LocRange(Loc(4, 1), Loc(4, 6)) after LocRange(Loc(1, 2), Loc(4, 2))))
  }

  test("2:1-3:4 intersects 1:5-4:3") {
    assert(LocRange(Loc(2, 1), Loc(3, 4)) intersects LocRange(Loc(1, 5), Loc(4, 3)))
  }

  test("2:1-3:4 intersects 3:4-4:3") {
    assert(LocRange(Loc(2, 1), Loc(3, 4)) intersects LocRange(Loc(3, 4), Loc(4, 3)))
  }

  test("2:1-3:4 does not intersect 4:4-4:3") {
    assert(!(LocRange(Loc(2, 1), Loc(3, 4)) intersects LocRange(Loc(4, 4), Loc(4, 3))))
  }

  test("2:1-3:4 not_intersect 4:4-4:3") {
    assert(LocRange(Loc(2, 1), Loc(3, 4)) not_intersect LocRange(Loc(4, 4), Loc(4, 3)))
  }

  test("2:1-3:4 inside 1:5-4:3") {
    assert(LocRange(Loc(2, 1), Loc(3, 4)) inside LocRange(Loc(1, 5), Loc(4, 3)))
  }

  test("1:4-3:4 not inside 1:5-4:3") {
    assert(!(LocRange(Loc(1, 4), Loc(3, 4)) inside LocRange(Loc(1, 5), Loc(4, 3))))
  }
}
