package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

import at.forsyte.apalache.tla.lir.convenience._

@RunWith(classOf[JUnitRunner])
class TestKeramelizer extends FunSuite with BeforeAndAfterEach {
  private var keramelizer = new Keramelizer(TrackerWithListeners())

  override def beforeEach(): Unit = {
    keramelizer = new Keramelizer(TrackerWithListeners())
  }

  test("intersect") {
    val input = tla.cap(tla.name("X"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected = tla.filter(tla.name("x"),
      tla.name("X"),
      tla.in(tla.name("x"), tla.name("Y")))
    assert(expected == output)
  }
}