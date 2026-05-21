package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Checker.{Deadlock, Error, NoError}
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams.InvariantMode
import at.forsyte.apalache.tla.bmcmt.trex.{
  FilteredTransitionExecutor, IncrementalExecutionContext, TransitionExecutorImpl,
}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla
import org.scalatest.funsuite.FixtureAnyFunSuite
import scala.collection.immutable.SortedMap

trait TestSeqModelCheckerTrait extends FixtureAnyFunSuite {
  protected type FixtureParam = SymbStateRewriter

  private val intTag: Typed[TlaType1] = Typed(IntT1)
  private val recordT = RecT1(SortedMap("x" -> IntT1))
  private val historyT = SeqT1(recordT)
  private val boolOper0T = OperT1(Seq(), BoolT1)

  private def mkModuleWithX(): TlaModule = {
    TlaModule("root", List(TlaVarDecl("x")(Typed(IntT1))))
  }

  private def mkModuleWithXandY(): TlaModule = {
    TlaModule("root", List(TlaVarDecl("x")(intTag), TlaVarDecl("y")(intTag)))
  }

  private def assertResultHasNErrors(n: Int, result: Checker.CheckerResult) = assert(result match {
    case Error(m, _) if m == n => true
    case _                     => false
  })

  private def buildTransitions(transitions: TBuilderInstruction*): List[TlaEx] =
    transitions.map(_.build).toList

  test("Init + Inv => OK") { rewriter: SymbStateRewriter =>
    // x' <- 2
    val initTrans = buildTransitions(mkAssign("x", 2))
    val nextTrans = buildTransitions(mkAssign("x", 2))
    val notInvEx = tla.gt(tla.name("x", IntT1), tla.int(10))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, Map())
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Inv => ERR") { rewriter: SymbStateRewriter =>
    // x' <- 2
    val initTrans = buildTransitions(mkAssign("x", 2))
    val nextTrans = buildTransitions(mkAssign("x", 2))
    val notInvEx = tla.lt(tla.name("x", IntT1), tla.int(10))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, Map())
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("ConstInit + Init => OK") { rewriter: SymbStateRewriter =>
    // N' <- 10
    val cinit = mkAssign("N", 10).build
    // x' <- N
    val initTrans = buildTransitions(mkAssign("x", tla.name("N", IntT1), IntT1))
    val nextTrans = buildTransitions(mkAssign("x", tla.name("N", IntT1), IntT1))
    val module = TlaModule("root", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag)))
    val notInvEx = tla.lt(tla.name("x", IntT1), tla.int(10))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build

    val checkerInput = new CheckerInput(module, initTrans, nextTrans, Some(cinit), CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, Map())
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("ConstInit + Init => ERR") { rewriter: SymbStateRewriter =>
    // N' <- 10
    val cinit = mkAssign("N", 5).build
    // x' <- N
    val initTrans = buildTransitions(mkAssign("x", tla.name("N", IntT1), IntT1))
    val nextTrans = buildTransitions(mkAssign("x", tla.name("N", IntT1), IntT1))
    val module = new TlaModule("root", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag)))
    val notInvEx = tla.lt(tla.name("x", IntT1), tla.int(10))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build

    val checkerInput = new CheckerInput(module, initTrans, nextTrans, Some(cinit), CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, Map())
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(outcome match { case Error(1, _) => true; case _ => false })
  }

  test("Init, deadlock") { rewriter: SymbStateRewriter =>
    // x' <- 2 /\ x' <- 1
    val initTrans = buildTransitions(tla.and(mkAssign("x", 2), mkNotAssign("x", 1)))
    val nextTrans = buildTransitions(mkAssign("x", 2))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(outcome match { case Deadlock(_) => true; case _ => false })
  }

  test("Init, 2 options, OK") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    val nextTrans = buildTransitions(mkAssign("x", 2))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 1 => OK") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 1, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 10 + Inv (before + no-all-enabled) => ERR") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x < 5
    val invEx = tla.lt(tla.name("x", IntT1), tla.int(5))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = true
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 10 + Inv (before + all-enabled) => ERR") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x < 5
    val invEx = tla.lt(tla.name("x", IntT1), tla.int(5))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = false
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 10 + ActionInv (before + all-enabled) => ERR") { rewriter: SymbStateRewriter =>
    // x' := 2 \/ x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x' < x
    val invEx = tla.lt(tla.prime(tla.name("x", IntT1)), tla.name("x", IntT1))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = false
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 10 + ActionInv (before + all-enabled) => OK") { rewriter: SymbStateRewriter =>
    // x' := 2 \/ x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x' > x
    val invEx = tla.gt(tla.prime(tla.name("x", IntT1)), tla.name("x", IntT1))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = false
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 10 + Inv (after + all-enabled) => ERR") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x < 5
    val invEx = tla.lt(tla.name("x", IntT1), tla.int(5))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = false
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 10 + Inv (after + no-all-enabled) => ERR") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x < 5
    val invEx = tla.lt(tla.name("x", IntT1), tla.int(5))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = true
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 10 + ActionInv (after + all-enabled) => ERR") { rewriter: SymbStateRewriter =>
    // x' := 2 \/ x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x' < x
    val invEx = tla.lt(tla.prime(tla.name("x", IntT1)), tla.name("x", IntT1))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = false
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 10 + ActionInv (after + all-enabled) => OK") { rewriter: SymbStateRewriter =>
    // x' := 2 \/ x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x' > x
    val invEx = tla.gt(tla.prime(tla.name("x", IntT1)), tla.name("x", IntT1))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = false
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 10 + ActionInv (before) => ERR") { rewriter: SymbStateRewriter =>
    // x' := 2 \/ x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x' < x
    val invEx = tla.lt(tla.prime(tla.name("x", IntT1)), tla.name("x", IntT1))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = true
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 10 + ActionInv (before) => OK") { rewriter: SymbStateRewriter =>
    // x' := 2 \/ x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x' > x
    val invEx = tla.gt(tla.prime(tla.name("x", IntT1)), tla.name("x", IntT1))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = true
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 10 + ActionInv (after) => ERR") { rewriter: SymbStateRewriter =>
    // x' := 2 \/ x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x' < x
    val invEx = tla.lt(tla.prime(tla.name("x", IntT1)), tla.name("x", IntT1))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = true
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 10 + ActionInv (after) => OK") { rewriter: SymbStateRewriter =>
    // x' := 2 \/ x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x' > x
    val invEx = tla.gt(tla.prime(tla.name("x", IntT1)), tla.name("x", IntT1))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    params.discardDisabled = true
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 10 + TraceInv => OK") { rewriter: SymbStateRewriter =>
    // x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // TraceInv(hist) == hist[Len(hist)].x <= 10 + hist[1].x
    val hist = tla.name("hist", historyT)
    val invEx = tla.le(
        tla.app(tla.app(hist, tla.len(hist)), tla.str("x")),
        tla.plus(tla.int(10), tla.app(tla.app(hist, tla.int(1)), tla.str("x"))),
    )
    val inv = invEx.build
    val invDecl = TlaOperDecl("TraceInv", List(OperParam("hist", 0)), inv)(Untyped)
    val notInv = tla.not(invEx).build
    val notInvDecl = TlaOperDecl("TraceInv", List(OperParam("hist", 0)), notInv)(Untyped)
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List(), List((invDecl, notInvDecl))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 10 + TraceInv => ERR") { rewriter: SymbStateRewriter =>
    // x' := 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // TraceInv(hist) == hist[Len(hist)].x <= hist[1].x + 9
    val hist = tla.name("hist", historyT)
    val invEx = tla.le(
        tla.app(tla.app(hist, tla.len(hist)), tla.str("x")),
        tla.plus(tla.int(9), tla.app(tla.app(hist, tla.int(1)), tla.str("x"))),
    )
    val inv = invEx.build
    val invDecl = TlaOperDecl("TraceInv", List(OperParam("hist", 0)), inv)(Untyped)
    val notInv = tla.not(invEx).build
    val notInvDecl = TlaOperDecl("TraceInv", List(OperParam("hist", 0)), notInv)(Untyped)
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List(), List(), List((invDecl, notInvDecl))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next x 2 (LET-IN) + Inv => ERR") { rewriter: SymbStateRewriter =>
    // x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 1))
    // x' <- x + 1
    val assign = mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1)
    val nextTrans = buildTransitions(assign)
    // x < 3
    val pred = tla.lt(tla.name("x", IntT1), tla.int(3))
    val letDef = tla.letIn(tla.appOp(tla.name("Foo", boolOper0T)), tla.decl("Foo", pred))
    val inv = letDef.build
    val notInv = tla.not(letDef).build

    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 2, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("determinstic Init + 2 steps (regression)") { rewriter: SymbStateRewriter =>
    // y' <- 1 /\ x' <- 1
    val initTrans = buildTransitions(tla.and(mkAssign("y", 1), mkAssign("x", 1)))
    // y' <- y + 1 /\ x' <- x + 1
    val nextTrans = buildTransitions(tla.and(
            mkAssign("y", tla.plus(tla.name("y", IntT1), tla.int(1)), IntT1),
            mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1),
        )) ///
    val invEx = tla.eql(
        tla.eql(tla.int(3), tla.name("x", IntT1)),
        tla.eql(tla.int(3), tla.name("y", IntT1)),
    )
    val inv = invEx.build
    val notInv = tla.not(invEx).build

    val checkerInput =
      new CheckerInput(
          mkModuleWithXandY(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 2, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 1 => deadlock") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x > 3 /\ x' <- x + 1
    val nextTrans =
      buildTransitions(tla.and(
          tla.gt(tla.name("x", IntT1), tla.int(3)),
          mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1),
      ))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 1, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(outcome match { case Deadlock(_) => true; case _ => false })
  }

  test("Init + Next, 10 steps, OK") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 10 => deadlock") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x < 10 /\ x' <- x + 1
    val nextTrans =
      buildTransitions(tla.and(
          tla.lt(tla.name("x", IntT1), tla.int(10)),
          mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1),
      ))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(outcome match { case Deadlock(_) => true; case _ => false })
  }

  test("Init + Next + Inv x 10 => OK") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x < 100
    val invEx = tla.lt(tla.name("x", IntT1), tla.int(100))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next + Inv x 3 => ERR, edge case") { rewriter: SymbStateRewriter =>
    // the invariant is violated in the last state of a bounded execution

    // x' <- 0
    val initTrans = buildTransitions(mkAssign("x", 0))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x /= 3
    val notInvEx = tla.eql(tla.name("x", IntT1), tla.int(3))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 3, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next + Inv x 2 => OK, edge case") { rewriter: SymbStateRewriter =>
    // the invariant is violated in the last state of a bounded execution
    // x' <- 0
    val initTrans = buildTransitions(mkAssign("x", 0))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x /= 3
    val notInvEx = tla.eql(tla.name("x", IntT1), tla.int(3))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 2, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next + Inv x 10 and invariantFilter => OK") { rewriter: SymbStateRewriter =>
    // x' <- 2 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = buildTransitions(mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1))
    // x < 5
    val invEx = tla.lt(tla.name("x", IntT1), tla.int(5))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    // initialize the model checker
    // We require the invariant to be checked only after the second step. So we will miss invariant violation.
    val tuning = Map("search.invariantFilter" -> "2")
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, tuning)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex =
      new FilteredTransitionExecutor("", params.invFilter, new TransitionExecutorImpl(params.consts, params.vars, ctx))
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 3 + non-determinism => no deadlock") { rewriter: SymbStateRewriter =>
    // x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 1))
    // x' <- x + 1 \/ x > 100 /\ x' <- x
    val trans1 = mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1)
    val trans2 = tla.and(
        tla.gt(tla.name("x", IntT1), tla.int(100)),
        mkAssign("x", tla.name("x", IntT1), IntT1),
    )
    val nextTrans = buildTransitions(trans1, trans2)
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 3, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next, 10 steps, non-determinism in init and next") { rewriter: SymbStateRewriter =>
    // x' <- 0 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 0), mkAssign("x", 1))
    // x' <- x + 1 \/ x > 10 /\ x' <- x
    val trans1 = mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1)
    val trans2 = tla.and(
        tla.gt(tla.name("x", IntT1), tla.int(10)),
        mkAssign("x", tla.name("x", IntT1), IntT1),
    )
    val nextTrans = buildTransitions(trans1, trans2)
    // ~(x <= 10)
    val notInvEx = tla.gt(tla.name("x", IntT1), tla.int(10))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("cInit + Init + Next, 10 steps") { rewriter: SymbStateRewriter =>
    // x' <- 0 \/ x' <- 1
    val initTrans = buildTransitions(mkAssign("x", 0), mkAssign("x", 1))
    // x' <- x + 1 \/ x > 10 /\ x' <- x
    val trans1 = mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1)
    val trans2 = tla.and(
        tla.gt(tla.name("x", IntT1), tla.int(10)),
        mkAssign("x", tla.name("x", IntT1), IntT1),
    )
    val nextTrans = buildTransitions(trans1, trans2)
    // a constant initializer: \E t \in { 20, 10 }: N' \in {t}
    val cInit =
      tla.skolem(tla.exists(
          tla.name("t", IntT1),
          tla.enumSet(tla.int(20), tla.int(10)),
          mkAssign("N", tla.name("t", IntT1), IntT1),
      ))
        .build

    // ~(x <= N)
    val notInvEx = tla.gt(tla.name("x", IntT1), tla.name("N", IntT1))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build
    val dummyModule = TlaModule("root", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag)))
    val checkerInput =
      new CheckerInput(
          dummyModule,
          initTrans,
          nextTrans,
          Some(cInit),
          CheckerInputVC(List((inv, notInv))),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, Map())
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(1, outcome)
  }

  test("Init + Next, 10 steps and filter") { rewriter: SymbStateRewriter =>
    // x' <- 0
    val initTrans = buildTransitions(mkAssign("x", 0))
    // x' <- x + 1 \/ x' <- x + 2
    val trans1 = mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1)
    val trans2 = mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(2)), IntT1)
    val nextTrans = buildTransitions(trans1, trans2)
    // ~(x <= 11)
    val notInvEx = tla.gt(tla.name("x", IntT1), tla.int(11))
    val notInv = notInvEx.build
    val inv = tla.not(notInvEx).build
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
    // initialize the model checker
    val tuning = Map.empty[String, String] // Map("search.transitionFilter" -> filter)
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, tuning)
    val ctx = new IncrementalExecutionContext(rewriter)
    val impl = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val trex = new FilteredTransitionExecutor("([0-9]|10)->0", "", impl)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assert(NoError() == outcome)
  }

  test("Init + Next x 2 + Inv + View => ERR x 4") { rewriter: SymbStateRewriter =>
    // x' <- 0
    val initTrans = buildTransitions(mkAssign("x", 0))
    // x' := x + 1 \/ x' := x - 1 \/ x' := x
    val action1 = mkAssign("x", tla.plus(tla.name("x", IntT1), tla.int(1)), IntT1)
    val action2 = mkAssign("x", tla.minus(tla.name("x", IntT1), tla.int(1)), IntT1)
    val action3 = mkAssign("x", tla.name("x", IntT1), IntT1)
    val nextTrans = buildTransitions(action1, action2, action3)
    // x = 0
    val invEx = tla.eql(tla.name("x", IntT1), tla.int(0))
    val inv = invEx.build
    val notInv = tla.not(invEx).build
    // view: <<x < 0, x > 0>>
    val view = tla.tuple(tla.le(tla.name("x", IntT1), tla.int(0)), tla.ge(tla.name("x", IntT1), tla.int(0)))
      .build
    val checkerInput =
      new CheckerInput(
          mkModuleWithX(),
          initTrans,
          nextTrans,
          None,
          CheckerInputVC(List((inv, notInv)), List.empty, List.empty, Some(view)),
      )
    val params = new ModelCheckerParams(checkerInput, stepsBound = 2, Map())
    // we expect 4 errors, but an upper bound may be larger
    params.nMaxErrors = 10
    params.discardDisabled = true
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(ModelCheckerContext(params, checkerInput, trex))
    val outcome = checker.run()
    assertResultHasNErrors(4, outcome)
  }

  private def mkAssign(varName: String, value: Int): TBuilderInstruction = {
    tla.assign(tla.prime(tla.name(varName, IntT1)), tla.int(value))
  }

  private def mkAssign(varName: String, rhs: TBuilderInstruction, tt: TlaType1): TBuilderInstruction = {
    tla.assign(tla.prime(tla.name(varName, tt)), rhs)
  }

  private def mkNotAssign(varName: String, value: Int): TBuilderInstruction = {
    tla.eql(tla.prime(tla.name(varName, IntT1)), tla.int(value))
  }

}
