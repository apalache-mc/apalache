package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSmtFreeSTE extends FunSuite with TestingPredefs {

  val sourceLoc = new SourceLocator(Map.empty, new ChangeListener)

  val ste = new SmtFreeSymbolicTransitionExtractor(TrackerWithListeners(), sourceLoc)

  test("Single ex: candidate") {
    val ex = tla.primeEq(n_x, tla.int(1)).untyped()
    val vars = Set("x")
    val strat = ste.getStrategy(vars, ex)

    assert(strat == Seq(ex.ID))
  }

  test("Single ex: manual asgn") {
    val ex = tla.assignPrime(n_x, tla.int(1)).untyped()
    val vars = Set("x")
    val strat = ste.getStrategy(vars, ex)

    assert(strat == Seq(ex.ID))
  }

  test("2 candidates: Manual / natural") {
    val manual = tla.assignPrime(n_x, tla.int(1)).untyped()
    val natural = tla.primeEq(n_x, tla.int(1)).untyped()
    val vars = Set("x")

    val ex1 = tla.and(manual, natural).untyped()
    val strat1 = ste.getStrategy(vars, ex1)

    assert(strat1 == Seq(manual.ID))

    val ex2 = tla.and(natural, manual).untyped()
    assertThrows[AssignmentException] {
      ste.getStrategy(vars, ex2)
    }

  }

  test("Missing var") {
    val ex = tla.primeEq(n_x, tla.int(1)).untyped()
    val vars = Set("x", "y")

    assertThrows[AssignmentException] {
      ste.getStrategy(vars, ex)
    }
  }

  test("Assignment in LET-IN") {
    val asgn = tla.primeEq(n_x, tla.int(1)).untyped()
    val declA = tla.declOp("A", asgn).untypedOperDecl()
    val ex = tla.letIn(tla.appDecl(declA), declA).untyped()

    val vars = Set("x")

    val strat = ste.getStrategy(vars, ex)

    assert(strat == Seq(asgn.ID))

    // A is non-nullary, B is external
    val asgn2 = tla.primeEq(n_x, tla.int(1)).untyped()
    val declA2 = tla.declOp("A", asgn2, "p").untypedOperDecl()
    val asgn3 = tla.primeEq(n_y, tla.int(1)).untyped()
    val declB = tla.declOp("B", asgn3).untypedOperDecl()
    val ex2 = tla
      .letIn(
          tla.and(
              tla.appDecl(declA2, tla.int(1)),
              tla.appDecl(declB)
          ), declA2)
      .untyped()

    val vars2 = Set("x", "y")

    val strat2 = ste.getStrategy(vars2, ex2, BodyMapFactory.makeFromDecl(declB))

    assert(strat2 == Seq(asgn2.ID, asgn3.ID))
  }

  test("Recursive operators") {
    // Recursive operators cannot introduce assignments,
    // but are still subject to assignment-before-use rules
    val asgnInRec = tla.primeEq(n_x, tla.int(1)).untyped()
    val asgn = tla.primeEq(n_x, tla.int(1)).untyped()
    val declA = tla.declOp("A", asgnInRec).untypedOperDecl()
    declA.isRecursive = true // just the flag matters
    val ex1 = tla.and(asgn, tla.appDecl(declA))
    val ex2 = tla.and(tla.appDecl(declA), asgn)

    val vars = Set("x")

    val operMap = BodyMapFactory.makeFromDecl(declA)
    val strat1 = ste.getStrategy(vars, ex1, operMap)

    assert(strat1 == Seq(asgn.ID))

    assertThrows[AssignmentException] {
      ste.getStrategy(vars, ex2, operMap)
    }
  }

  test("Disjunction") {
    val asgn1 = tla.primeEq(n_x, tla.int(1)).untyped()
    val asgn2 = tla.primeEq(n_x, tla.int(2)).untyped()
    val ex = tla.or(asgn1, asgn2).untyped()
    val vars = Set("x")
    val strat = ste.getStrategy(vars, ex)

    assert(strat == Seq(asgn1.ID, asgn2.ID))
  }

  test("Use before assignment") {
    val asgn = tla.primeEq(n_x, tla.int(1)).untyped()
    val cmp = tla.gt(tla.prime(n_x), tla.int(0)).untyped()
    val ex = tla.and(cmp, asgn).untyped()
    val vars = Set("x")

    assertThrows[AssignmentException] {
      ste.getStrategy(vars, ex)
    }
  }

}
