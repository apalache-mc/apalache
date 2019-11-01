package at.forsyte.apalache.tla.pp

import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestUniqueNameGenerator extends FunSuite with BeforeAndAfterEach {
  test("first three") {
    val gen = new UniqueNameGenerator
    assert("t_1" == gen.newName())
    assert("t_2" == gen.newName())
    assert("t_3" == gen.newName())
  }

  test("after 10000") {
    val gen = new UniqueNameGenerator
    for (i <- 1.to(10000)) {
      gen.newName()
    }
    assert("t_7pt" == gen.newName())
  }
}
