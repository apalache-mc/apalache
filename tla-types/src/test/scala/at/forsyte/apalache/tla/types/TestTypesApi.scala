package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.{build, TBuilderTypeException}
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

/**
 * Test the API provided by the types package.
 */
@RunWith(classOf[JUnitRunner])
class TestTypesApi extends AnyFunSuite {
  test("tla builder constructs TlaEx") {
    // build TlaEx via an implicit conversion
    val ex: TlaEx = tla.plus(tla.int(2), tla.int(3))
    assert(ex.isInstanceOf[OperEx])
    assert(ex.typeTag == Typed(IntT1))
  }

  test("tla builder errors when ill-typed") {
    assertThrows[TBuilderTypeException] {
      // build TlaEx via an implicit class that enriches the instruction with the method `build`.
      tla.plus(tla.int(2), tla.bool(true)).build
    }
  }

  test("tla builder constructs TlaOperDecl") {
    val x = tla.name("x", IntT1)
    // build an operator declaration via an implicit conversion
    val decl: TlaOperDecl = tla.decl("Double", tla.plus(x, x), tla.param("x", IntT1))
    assert(decl.isInstanceOf[TlaOperDecl])
  }

  test("tla builder constructs TlaOperDecl via a type class") {
    val x = tla.name("x", IntT1)
    // build an operator declaration via an implicit conversion
    val decl = tla.decl("Double", tla.plus(x, x), tla.param("x", IntT1)).build
    assert(decl.isInstanceOf[TlaOperDecl])
  }

}
