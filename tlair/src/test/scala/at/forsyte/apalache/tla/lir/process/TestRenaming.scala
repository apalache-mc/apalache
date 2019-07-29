package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Test variable renaming.
  */
@RunWith(classOf[JUnitRunner])
class TestRenaming extends FunSuite {
  test("test renaming exists/forall") {
    val renaming = new Renaming()
    val original =
        tla.and(
          tla.exists(tla.name("x"), tla.name("S"), tla.gt(tla.name("x"), tla.int(1))),
          tla.forall(tla.name("x"), tla.name("T"), tla.lt(tla.name("x"), tla.int(42))))
    ///
    val expected =
      tla.and(
        tla.exists(tla.name("x"), tla.name("S"), tla.gt(tla.name("x"), tla.int(1))),
        tla.forall(tla.name("x2"), tla.name("T"), tla.lt(tla.name("x2"), tla.int(42))))
    val renamed = renaming.renameBindingsUnique(original)
    assert(expected == renamed)
  }

  test("test renaming filter") {
    val renaming = new Renaming()
    val original =
        tla.cup(
          tla.filter(tla.name("x"), tla.name("S"), tla.eql(tla.name("x"), tla.int(1))),
          tla.filter(tla.name("x"), tla.name("S"), tla.eql(tla.name("x"), tla.int(2)))
        )
    val expected =
      tla.cup(
        tla.filter(tla.name("x"), tla.name("S"), tla.eql(tla.name("x"), tla.int(1))),
        tla.filter(tla.name("x2"), tla.name("S"), tla.eql(tla.name("x2"), tla.int(2))))
    val renamed = renaming.renameBindingsUnique(original)
    assert(expected == renamed)
  }
}
