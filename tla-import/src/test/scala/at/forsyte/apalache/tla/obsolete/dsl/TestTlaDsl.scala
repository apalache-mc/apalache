package at.forsyte.apalache.tla.obsolete.dsl

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import Implicit._

/**
 * Tests for DSL
 *
 * @author konnov
 */
@RunWith(classOf[JUnitRunner])
class TestTlaDsl extends FunSuite {
  test("all in one") {
    /*
    val b = new Builder
    // top-level definitions
    val m = b MODULE 'foo
    m EXTENDS 'M1
    m CONSTANTS ('n, 't)
    m VARIABLES 'x
    m ASSUME 42
    m OPER 'F ARGS ('a, 'b) DEF 42
    m OPER 'G ARGS ('a, 'b) DEF "baz"
    m INSTANCE 'M1
    m INSTANCE 'M2 WITH ('p1 -> 1, 'p2 -> 3)

    // set operations
    m OPER 'OPER1 DEF SetEnum(1, 2, 3) CUP SetFilter('x, 'S, TRUE) CUP SetMap('x, 'S, 42) CAP SUBSET SetEnum(1, 2)

    assert("foo" == m.name)
    */
  }
}
