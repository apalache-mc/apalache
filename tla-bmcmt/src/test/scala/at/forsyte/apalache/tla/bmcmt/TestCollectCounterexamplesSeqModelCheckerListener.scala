package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Checker.Error
import at.forsyte.apalache.tla.bmcmt.analyses.ExprGradeStoreImpl
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.bmcmt.trex.{IncrementalExecutionContext, TransitionExecutorImpl}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestCollectCounterexamplesModelCheckerListener extends AnyFunSuite {

  private val types = Map("i" -> IntT1(), "b" -> BoolT1())

  private def mkAssign(varName: String, value: Int): TlaEx = {
    assign(prime(name(varName) ? "i") ? "i", int(value)).typed(types, "b")
  }

  test("finds cex for invariant violation at initial state") {
    // construct TLA+ module
    val initTrans = List(mkAssign("x", 2))
    val nextTrans = List(mkAssign("x", 2))
    // Inv == x != 2
    val notInv = eql(name("x") ? "i", int(2)).typed(types, "b")
    val inv = not(notInv).typed(types, "b")
    val module = TlaModule("root", List(TlaVarDecl("x")(Typed(IntT1()))))

    // construct checker input + parameters
    val checkerInput = new CheckerInput(module, initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, 0, Map(), false)

    // create utility objects
    val solver = RecordingSolverContext.createZ3(None, SolverConfig.default)
    val rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)

    // run the model checker with listener
    val listener = new CollectCounterexamplesModelCheckerListener()
    val checker = new SeqModelChecker(params, checkerInput, trex, Seq(listener))

    // check the outcome
    val outcome = checker.run()
    assert(Error(1) == outcome)

    // check the counterexample
    assert(listener.counterExamples.length == 1)
    val cex = listener.counterExamples.head.path
    assert(cex.length == 2) // () --(init transition)--> initial state
    assert(cex.forall(_._2 == 0)) // state number
    assert(cex.head._1.isEmpty) // empty binding on 0th state
    val (binding, _) = cex.last
    assert(binding.contains("x"))
    val valOfX = binding("x")
    assert(valOfX.isInstanceOf[ValEx])
    assert(valOfX.asInstanceOf[ValEx] == int(2).typed(types, "i"))
  }

  test("finds cex for invariant violation after one step") {
    // construct TLA+ module
    val initTrans = List(mkAssign("x", 10))
    val nextTrans = List(mkAssign("x", 2))
    // Inv == x != 2
    val notInv = eql(name("x") ? "i", int(2)).typed(types, "b")
    val inv = not(notInv).typed(types, "b")
    val module = TlaModule("root", List(TlaVarDecl("x")(Typed(IntT1()))))

    // construct checker input + parameters
    val checkerInput = new CheckerInput(module, initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, 1, Map(), false)

    // create utility objects
    val solver = RecordingSolverContext.createZ3(None, SolverConfig.default)
    val rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)

    // run the model checker with listener
    val listener = new CollectCounterexamplesModelCheckerListener()
    val checker = new SeqModelChecker(params, checkerInput, trex, Seq(listener))

    // check the outcome
    val outcome = checker.run()
    assert(Error(1) == outcome)

    // check the counterexample
    assert(listener.counterExamples.length == 1)
    val cex = listener.counterExamples.head.path
    assert(cex.length == 3) // () --(init transition)--> initial state
    assert(cex.forall(_._2 == 0)) // state number
    assert(cex.head._1.isEmpty) // empty binding on 0th state
    val (binding, _) = cex.last
    assert(binding.contains("x"))
    val valOfX = binding("x")
    assert(valOfX.isInstanceOf[ValEx])
    assert(valOfX.asInstanceOf[ValEx] == int(2).typed(types, "i"))
  }

  test("collects multiple cex") {
    // construct TLA+ module
    val initTrans = List(mkAssign("x", 10))
    val nextTrans = List(mkAssign("x", 2))
    // Inv == x != 2
    val notInv = eql(name("x") ? "i", int(2)).typed(types, "b")
    val inv = not(notInv).typed(types, "b")
    val module = TlaModule("root", List(TlaVarDecl("x")(Typed(IntT1()))))

    // construct checker input + parameters
    val checkerInput = new CheckerInput(module, initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, 1, Map(), false) { nMaxErrors = 3 }

    // create utility objects
    val solver = RecordingSolverContext.createZ3(None, SolverConfig.default)
    val rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)

    // run the model checker with listener
    val listener = new CollectCounterexamplesModelCheckerListener()
    val checker = new SeqModelChecker(params, checkerInput, trex, Seq(listener))

    // check the outcome
    val outcome = checker.run()
    assert(Error(3) == outcome)

    // check the counterexample
    assert(listener.counterExamples.length == 3)
  }
}
