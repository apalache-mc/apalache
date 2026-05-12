package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTSolver
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.types.{tlaU => tla}
import at.forsyte.apalache.tla.typecomp._
import io.github.cvc5.{CVC5ApiException, Kind, Solver, TermManager}
import org.scalatest.funsuite.AnyFunSuite

class TestCvc5SolverContext extends AnyFunSuite {
  private val cvc5Config = SolverConfig.default.copy(smtSolver = SMTSolver.CVC5, z3StatsSec = 0)

  test("assert and evaluate an integer cell") {
    val solver = new Cvc5SolverContext(cvc5Config)
    try {
      val arena = PureArenaAdapter.create(solver).appendCell(IntT1)
      val x = arena.topCell

      solver.assertGroundExpr(tla.eql(x.toBuilder, tla.int(42)))

      assert(solver.sat())
      assert(solver.evalGroundExpr(x.toBuilder) == tla.int(42).build)
    } finally {
      solver.dispose()
    }
  }

  test("push and pop assertions") {
    val solver = new Cvc5SolverContext(cvc5Config)
    try {
      val arena = PureArenaAdapter.create(solver).appendCell(IntT1)
      val x = arena.topCell

      solver.assertGroundExpr(tla.eql(x.toBuilder, tla.int(42)))
      assert(solver.sat())

      solver.push()
      solver.assertGroundExpr(tla.gt(x.toBuilder, tla.int(100)))
      assert(!solver.sat())

      solver.pop()
      assert(solver.sat())
    } finally {
      solver.dispose()
    }
  }

  test("cvc5 requires arrays-exp for constant arrays") {
    val termManager = new TermManager()
    val solver = new Solver(termManager)
    try {
      val intSort = termManager.getIntegerSort
      val arraySort = termManager.mkArraySort(intSort, intSort)
      val f = termManager.mkConst(arraySort, "f")
      val default = termManager.mkConstArray(arraySort, termManager.mkInteger(0))

      // default = const 0
      // (= f default)
      solver.assertFormula(termManager.mkTerm(Kind.EQUAL, f, default))

      val error = intercept[CVC5ApiException] {
        solver.checkSat()
      }
      assert(
          error.getMessage == "Cannot handle assertion with term of kind STORE_ALL in this configuration. Try --arrays-exp.")
    } finally {
      solver.deletePointer()
      termManager.deletePointer()
    }
  }

  test("cvc5 rejects equality between store chains over different constant arrays") {
    val termManager = new TermManager()
    val solver = new Solver(termManager)
    try {
      solver.setOption("arrays-exp", "true")

      val intSort = termManager.getIntegerSort
      val arraySort = termManager.mkArraySort(intSort, intSort)
      val k1 = termManager.mkConst(intSort, "k1")
      val k2 = termManager.mkConst(intSort, "k2")
      val v1 = termManager.mkConst(intSort, "v1")
      val v2 = termManager.mkConst(intSort, "v2")

      val f = termManager.mkConstArray(arraySort, termManager.mkInteger(0))
      val g = termManager.mkConstArray(arraySort, termManager.mkInteger(1))
      val f1 = termManager.mkTerm(Kind.STORE, f, k1, v1)
      val g1 = termManager.mkTerm(Kind.STORE, g, k2, v2)

      // f = const 0
      // g = const 1
      // (= f1 (store f k1 v1))
      // (= g1 (store g k2 v2))
      // (= f1 g1)

      solver.assertFormula(termManager.mkTerm(Kind.EQUAL, f, f))
      solver.assertFormula(termManager.mkTerm(Kind.EQUAL, g, g))
      solver.assertFormula(termManager.mkTerm(Kind.EQUAL, f1, g1))

      val error = intercept[CVC5ApiException] {
        solver.checkSat()
      }
      assert(
          error.getMessage == "Array theory solver does not yet support write-chains connecting two different constant arrays")
    } finally {
      solver.deletePointer()
      termManager.deletePointer()
    }
  }

}
