package at.forsyte.apalache.tla.bmcmt

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, SolverConfig, SolverContext, Z3SolverContext}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.scalatest.{fixture, BeforeAndAfterEach}

trait RewriterBase extends fixture.FunSuite with BeforeAndAfterEach {
  protected type FixtureParam = String

  protected val oopsla19RewriterType = "oopsla19"
  protected val arraysRewriterType = "arrays"

  protected var solverContext: SolverContext = _
  protected var arena: Arena = _

  override def beforeEach() {
    solverContext = new PreproSolverContext(new Z3SolverContext(SolverConfig.default.copy(debug = true)))
    arena = Arena.create(solverContext)
  }

  override def afterEach() {
    solverContext.dispose()
  }

  protected def create(rewriterType: String): SymbStateRewriter = {
    rewriterType match {
      case `oopsla19RewriterType` => new SymbStateRewriterAuto(solverContext)
      case `arraysRewriterType`   => new SymbStateRewriterAutoWithArrays(solverContext)
      case oddRewriterType        => throw new IllegalArgumentException(s"Unexpected rewriter of type $oddRewriterType")
    }
  }

  protected def createWithoutCache(rewriterType: String): SymbStateRewriter = {
    rewriterType match {
      case `oopsla19RewriterType` => new SymbStateRewriterImpl(solverContext)
      case `arraysRewriterType`   => new SymbStateRewriterImplWithArrays(solverContext)
      case oddRewriterType =>
        throw new IllegalArgumentException(s"Unexpected cacheless rewriter of type $oddRewriterType")
    }
  }

  protected def assertUnsatOrExplain(rewriter: SymbStateRewriter, state: SymbState): Unit = {
    assertOrExplain("UNSAT", rewriter, state, !solverContext.sat())
  }

  protected def assumeTlaEx(rewriter: SymbStateRewriter, state: SymbState): SymbState = {
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    nextState
  }

  protected def assertTlaExAndRestore(rewriter: SymbStateRewriter, state: SymbState): Unit = {
    rewriter.push()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    rewriter.pop()
  }

  private def assertOrExplain(msg: String, rewriter: SymbStateRewriter, state: SymbState, outcome: Boolean): Unit = {
    if (!outcome) {
      val writer = new StringWriter()
      new SymbStateDecoder(solverContext, rewriter).dumpArena(state, new PrintWriter(writer))
      solverContext.log(writer.getBuffer.toString)
      solverContext.push() // push and pop flush the log output
      solverContext.pop()
      fail("Expected %s, check log.smt for explanation".format(msg))
    }

  }
}
