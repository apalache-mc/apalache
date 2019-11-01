package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

import at.forsyte.apalache.tla.lir.convenience._

@RunWith(classOf[JUnitRunner])
class TestKeramelizer extends FunSuite with BeforeAndAfterEach {
  private var keramelizer = new Keramelizer(new UniqueNameGenerator(), TrackerWithListeners())

  override def beforeEach(): Unit = {
    keramelizer = new Keramelizer(new UniqueNameGenerator(), TrackerWithListeners())
  }

  test("""X \intersect Y""") {
    val input = tla.cap(tla.name("X"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected = tla.filter(tla.name("t_1"),
      tla.name("X"),
      tla.in(tla.name("t_1"), tla.name("Y")))
    assert(expected == output)
  }

  test("intersect under another expression") {
    val input =
      tla.cup(tla.name("Z"),
        tla.cap(tla.name("X"), tla.name("Y")))
    val output = keramelizer.apply(input)
    val transformed =
      tla.filter(tla.name("t_1"),
        tla.name("X"),
        tla.in(tla.name("t_1"), tla.name("Y")))
    val expected = tla.cup(tla.name("Z"), transformed)
    assert(expected == output)
  }

  test("""X \ Y""") {
    val input = tla.setminus(tla.name("X"), tla.name("Y"))
    val output = keramelizer.apply(input)
    val expected = tla.filter(tla.name("t_1"),
      tla.name("X"),
      tla.notin(tla.name("t_1"), tla.name("Y")))
    assert(expected == output)
  }
}