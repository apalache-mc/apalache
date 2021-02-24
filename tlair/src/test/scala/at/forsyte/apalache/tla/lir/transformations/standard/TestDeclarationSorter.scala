package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir._
import UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestDeclarationSorter extends FunSuite with BeforeAndAfterEach {
  test("Bar calls Foo out of order") {
    val foo = tla.declOp("Foo", tla.bool(true))
    val bar = tla.declOp("Bar", tla.appOp(tla.name("Foo")))
    val input = new TlaModule("test", List(bar, foo))
    val expected = new TlaModule("test", List(foo, bar))
    assert(expected == DeclarationSorter.instance(input))
  }

  test("Foo calls Bar calls Baz in order") {
    val foo = tla.declOp("Foo", tla.appOp(tla.name("Bar")))
    val bar = tla.declOp("Bar", tla.appOp(tla.name("Baz")))
    val baz = tla.declOp("Baz", tla.bool(true))
    val input = new TlaModule("test", List(baz, foo, bar))
    val expected = new TlaModule("test", List(baz, bar, foo))
    assert(expected == DeclarationSorter.instance(input))
  }

  test("Foo calls Bar in LET-IN calls Baz in order") {
    val foo = tla.declOp("Foo", tla.appOp(tla.name("Bar")))
    val letIn = tla.letIn(tla.bool(true), tla.declOp("local", tla.appOp(tla.name("Baz"))))
    val bar = tla.declOp("Bar", letIn)
    val baz = tla.declOp("Baz", tla.bool(true))
    val input = new TlaModule("test", List(baz, bar, foo))
    val expected = new TlaModule("test", List(baz, bar, foo))
    assert(expected == DeclarationSorter.instance(input))
  }

  test("Foo in a cycle") {
    val foo = tla.declOp("Foo", tla.appOp(tla.name("Bar")))
    val bar = tla.declOp("Bar", tla.appOp(tla.name("Baz")))
    val baz = tla.declOp("Baz", tla.appOp(tla.name("Foo")))
    val input = new TlaModule("test", List(foo, bar, baz))
    assertThrows[CyclicDependencyError](DeclarationSorter.instance(input))
  }

  test("Foo uses VARIABLE x out of order") {
    val foo = tla.declOp("Foo", tla.name("x"))
    val x = TlaVarDecl("x")
    val input = new TlaModule("test", List(foo, x))
    val expected = new TlaModule("test", List(x, foo))
    assert(expected == DeclarationSorter.instance(input))
  }

  test("Foo uses CONSTANT N out of order") {
    val foo = tla.declOp("Foo", tla.name("N"))
    val const = TlaConstDecl("N")
    val input = new TlaModule("test", List(foo, const))
    val expected = new TlaModule("test", List(const, foo))
    assert(expected == DeclarationSorter.instance(input))
  }

  test("preserve the order of constants and variables") {
    val foo = tla.declOp("Foo", tla.name("x"))
    val N = TlaConstDecl("N")
    val x = TlaVarDecl("x")
    val input = new TlaModule("test", List(foo, N, x))
    val expected = new TlaModule("test", List(N, x, foo))
    assert(expected == DeclarationSorter.instance(input))
  }

  test("Assume uses Foo out of order") {
    val foo = tla.declOp("Foo", tla.int(1))
    val assume = TlaAssumeDecl(tla.appOp(tla.name("Foo")))
    val input = new TlaModule("test", List(assume, foo))
    val expected = new TlaModule("test", List(foo, assume))
    assert(expected == DeclarationSorter.instance(input))
  }
}
