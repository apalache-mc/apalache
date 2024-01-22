package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite

import java.io.File

@RunWith(classOf[JUnitRunner])
class TestDeclarationSorter extends AnyFunSuite with BeforeAndAfterEach {
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
    val letIn = tla.letIn(tla.bool(true), tla.declOp("local", tla.appOp(tla.name("Baz"))).untypedOperDecl())
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
    val witnessFile = new File("dependencies.dot")
    assert(witnessFile.exists() == true)
    witnessFile.delete()
  }

  test("regression: a cycle hidden via a call") {
    // regression for #758
    val foo = tla.declOp("Foo", tla.int(1))
    val bar = tla.declOp("Bar", tla.appOp(tla.name("Foo"), tla.appOp(tla.name("Baz"))))
    val baz = tla.declOp("Baz", tla.appOp(tla.name("Foo"), tla.appOp(tla.name("Bar"))))
    val input = new TlaModule("test", List(foo, bar, baz))
    assertThrows[CyclicDependencyError](DeclarationSorter.instance(input))
    val witnessFile = new File("dependencies.dot")
    assert(witnessFile.exists() == true)
    witnessFile.delete()
  }

  test("regression: a false cycle") {
    // regression for #645

    // The following two declarations do not form a cycle, as Foo uses it's parameter 'pid', not calling the operator 'pid'.
    // Foo(pid) == 1
    val foo = tla.declOp("Foo", tla.name("pid"), OperParam("pid"))
    // pid == Foo(2)
    val pid = tla.declOp("pid", tla.appOp(tla.name("Foo"), tla.int(2)))
    val input = new TlaModule("test", List(foo, pid))
    val expected = new TlaModule("test", List(foo, pid))
    assert(expected == DeclarationSorter.instance(input))
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
    val assume = TlaAssumeDecl(None, tla.appOp(tla.name("Foo")))
    val input = TlaModule("test", List(assume, foo))
    val expected = TlaModule("test", List(foo, assume))
    assert(expected == DeclarationSorter.instance(input))
  }
}
