package at.forsyte.tlair

import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.junit.runner.RunWith

/**
 * @author konnov
 */
@RunWith(classOf[JUnitRunner])
class TestLocSuite extends FunSuite {
  test("Different lines are compared") {
    val lesser = new Loc(2, 3)
    val greater = new Loc(3, 4)
    assert(lesser.compare(greater) < 0)
  }
}
