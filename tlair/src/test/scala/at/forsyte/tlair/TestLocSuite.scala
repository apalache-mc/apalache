package at.forsyte.tlair

import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.junit.runner.RunWith

/**
 * Tests for Loc
 *
 * @see at.forsyte.tlair.Loc
 *
 * @author konnov
 */
@RunWith(classOf[JUnitRunner])
class TestLocSuite extends FunSuite {
  test("different lines are compared correctly") {
    val lesser = new Loc(2, 5)
    val greater = new Loc(3, 3)
    assert(lesser.compare(greater) < 0)
  }

  test("different columns are compared correctly") {
    val lesser = new Loc(3, 3)
    val greater = new Loc(3, 4)
    assert(lesser.compare(greater) < 0)
  }

  test("equal locations are reported equal") {
    val lesser = new Loc(3, 3)
    val greater = new Loc(3, 4)
    assert(lesser.compare(greater) < 0)
  }
}
