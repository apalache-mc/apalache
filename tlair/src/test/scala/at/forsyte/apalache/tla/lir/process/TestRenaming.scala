package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

/**
  * Test variable renaming.
  */
@RunWith(classOf[JUnitRunner])
class TestRenaming extends FunSuite with BeforeAndAfterEach {
  private var renaming = new Renaming(TrackerWithListeners())

  override protected def beforeEach(): Unit = {
    renaming = new Renaming(TrackerWithListeners())
  }

  test("test renaming exists/forall") {
    val original =
        tla.and(
          tla.exists(tla.name("x"), tla.name("S"), tla.gt(tla.name("x"), tla.int(1))),
          tla.forall(tla.name("x"), tla.name("T"), tla.lt(tla.name("x"), tla.int(42))))
    ///
    val expected =
      tla.and(
        tla.exists(tla.name("x1"), tla.name("S"), tla.gt(tla.name("x1"), tla.int(1))),
        tla.forall(tla.name("x2"), tla.name("T"), tla.lt(tla.name("x2"), tla.int(42))))
    val renamed = renaming.renameBindingsUnique(original)
    assert(expected == renamed)
  }

  test("test renaming filter") {
    val original =
        tla.cup(
          tla.filter(tla.name("x"), tla.name("S"), tla.eql(tla.name("x"), tla.int(1))),
          tla.filter(tla.name("x"), tla.name("S"), tla.eql(tla.name("x"), tla.int(2)))
        )
    val expected =
      tla.cup(
        tla.filter(tla.name("x1"), tla.name("S"), tla.eql(tla.name("x1"), tla.int(1))),
        tla.filter(tla.name("x2"), tla.name("S"), tla.eql(tla.name("x2"), tla.int(2))))
    val renamed = renaming.renameBindingsUnique(original)
    assert(expected == renamed)
  }

}
