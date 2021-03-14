package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker

@RunWith(classOf[JUnitRunner])
class TestManualAssignments extends FunSuite with TestingPredefs {

  val extr = new SymbolicTransitionExtractor(new IdleTracker)

  test("Single var - correct") {

    val vars = Seq("x")
    val ex = tla.or(tla.assignPrime(n_x, tla.int(1)), tla.assignPrime(n_x, tla.int(2)))

    val transitions = extr.apply(vars, ex)
    assert(transitions.nonEmpty)
  }

  test("Single var - incorrect") {

    val vars = Seq("x")
    //
    val ex = tla.or(tla.assignPrime(n_x, tla.int(1)), tla.primeEq(n_x, tla.int(2)))

    val transitions = extr.apply(vars, ex)
    assert(transitions.isEmpty)
  }

  test("Two manual vars - correct") {
    val vars = Seq("x", "y")
    val ex =
      tla.or(
          tla.and(tla.assignPrime(n_x, tla.int(1)), tla.assignPrime(n_y, tla.int(2))),
          tla.and(tla.assignPrime(n_x, tla.int(3)), tla.assignPrime(n_y, tla.int(4)))
      )
    val transitions = extr.apply(vars, ex)
    assert(transitions.nonEmpty)
  }

  test("Two manual vars - incorrect") {
    val vars = Seq("x", "y")
    val ex =
      tla.or(
          tla.and(tla.assignPrime(n_x, tla.int(1)), tla.assignPrime(n_y, tla.int(2))),
          tla.and(tla.assignPrime(n_x, tla.int(3)), tla.primeEq(n_y, tla.int(4)))
      )
    val transitions = extr.apply(vars, ex)
    assert(transitions.isEmpty)
  }

  test("Mixed vars - correct") {
    val vars = Seq("x", "y")
    val ex =
      tla.or(
          tla.and(tla.assignPrime(n_x, tla.int(1)), tla.primeEq(n_y, tla.int(2))),
          tla.and(tla.assignPrime(n_x, tla.int(3)), tla.primeEq(n_y, tla.int(4)))
      )
    val transitions = extr.apply(vars, ex)
    assert(transitions.nonEmpty)
  }

  test("Mixed vars - incorrect") {
    val vars = Seq("x", "y")
    val ex =
      tla.or(
          tla.and(tla.primeEq(n_x, tla.int(1)), tla.primeEq(n_y, tla.int(2))),
          tla.and(tla.assignPrime(n_x, tla.int(3)), tla.primeEq(n_y, tla.int(4)))
      )
    val transitions = extr.apply(vars, ex)
    assert(transitions.isEmpty)
  }

}
