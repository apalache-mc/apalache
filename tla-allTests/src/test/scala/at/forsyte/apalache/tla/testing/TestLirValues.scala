package at.forsyte.apalache.tla.testing

import at.forsyte.apalache.tla.lir._

import at.forsyte.apalache.tla.lir.predef.TlaIntSet
import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
 * Tests for the low-level intermediate representation.
 */
@RunWith(classOf[JUnitRunner])
class TestLirValues extends FunSuite {
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
    val c = new TlaConstDecl("x")
    assert("x" == c.name)
  }

  test("create a variable") {
    val c = new TlaVarDecl("x")
    assert("x" == c.name)
  }

  test("define a function") {
    val dom = TlaIntSet
    val f = TlaFun(dom)
    assert(f.domain == dom)
  }
}
