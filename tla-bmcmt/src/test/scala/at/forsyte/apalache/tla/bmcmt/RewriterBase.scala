package at.forsyte.apalache.tla.bmcmt

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.scalatest.fixture

trait RewriterBase extends fixture.FunSuite with EncodingBase {
  protected type FixtureParam = String

  protected var solverContext: SolverContext = _
  protected var arena: Arena = _

  protected def create(rewriterType: String): SymbStateRewriter = {
    rewriterType match {
      case `oopsla19EncodingType` => new SymbStateRewriterAuto(solverContext)
      case `arraysEncodingType`   => new SymbStateRewriterAutoWithArrays(solverContext)
      case oddRewriterType        => throw new IllegalArgumentException(s"Unexpected rewriter of type $oddRewriterType")
    }
  }

  protected def createWithoutCache(rewriterType: String): SymbStateRewriter = {
    rewriterType match {
      case `oopsla19EncodingType` => new SymbStateRewriterImpl(solverContext)
      case `arraysEncodingType`   => new SymbStateRewriterImplWithArrays(solverContext)
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
