package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.{LetInEx, TlaOperDecl}
import org.scalatest.{BeforeAndAfter, FunSuite}

/**
  * Tests of PrimePropagation.
  */
class TestPrimePropagation extends FunSuite with BeforeAndAfter {
  import tla._

  private var transformer: PrimePropagation = _

  before {
    transformer = new PrimePropagation(new IdleTracker, Set("x", "y"))
  }

  test("a name should not be primed") {
    val input = name("x")
    val output = transformer(input)
    assert(output == input)
  }

  test("a constant should not be primed") {
    val input = name("N")
    val output = transformer(input)
    assert(output == input)
  }

  test("a primed variable stays primed") {
    val input = prime(name("x"))
    val output = transformer(input)
    assert(output == input)
  }

  test("a primed literal is de-primed") {
    val intEx = int(2021)
    val input = prime(intEx)
    val output = transformer(input)
    assert(intEx == output)
  }

  test("a primed constant is de-primed") {
    val const = name("N")
    val input = prime(const)
    val output = transformer(input)
    assert(const == output)
  }

  test("prime is propagated in operator") {
    val input = prime(appFun(name("x"), name("y")))
    val output = transformer(input)
    val expected = appFun(prime(name("x")), prime(name("y")))
    assert(expected == output)
  }

  test("prime is propagated in LET-IN") {
    val fooDecl = TlaOperDecl("Foo", List.empty, appFun(name("x"), name("y")))
    val letIn = LetInEx(appOp("Foo"), fooDecl)
    val input = prime(letIn)
    val output = transformer(input)
    val expectedDecl =
      TlaOperDecl("Foo", List.empty, appFun(prime(name("x")), prime(name("y"))))
    val expectedLetIn = LetInEx(appOp("Foo"), expectedDecl)
    assert(expectedLetIn == output)
  }
}
