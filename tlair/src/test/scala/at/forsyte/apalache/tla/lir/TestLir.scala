package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
 * Tests for the low-level intermediate representation.
 */
@RunWith(classOf[JUnitRunner])
class TestLir extends FunSuite {
  test("create booleans") {
    val b = TlaBool(false)
    assert(!b.value)
    assert(!TlaFalse.value)
    assert(TlaTrue.value)
  }

  test("create int") {
    val i = TlaInt(1)
    assert(i.value == BigInt(1))
    assert(i == TlaInt(1))
    assert(i.isNatural)
    assert(TlaInt(0).isNatural)
    assert(!TlaInt(-1).isNatural)
  }

  test("create a string") {
    val s = TlaStr("hello")
    assert(s.value == "hello")
  }


  test("create a constant") {
    val c = new TlaConst("x")
    assert("x" == c.name)
  }

  test("create a variable") {
    val c = new TlaVar("x")
    assert("x" == c.name)
  }

  test("create a set") {
    val c = TlaEnumSet(Set(TlaInt(1), TlaInt(2), TlaInt(3)))
    assert(c.value.size == 3)
    assert(c.value == Set(TlaInt(1), TlaInt(2), TlaInt(3)))
  }

  test("create a set of functions") {
    val dom = TlaEnumSet(Set(TlaInt(1), TlaInt(2)))
    val range = TlaEnumSet(Set(TlaInt(2), TlaInt(3)))
    val s = TlaFunSet(dom, range)
    assert(s.elemDomain == dom)
    assert(s.elemRange == range)
  }

  test("define a function") {
    val dom = TlaEnumSet(Set(TlaInt(1), TlaInt(2)))
    val f = TlaFun(dom)
    assert(f.domain == dom)
  }
}
