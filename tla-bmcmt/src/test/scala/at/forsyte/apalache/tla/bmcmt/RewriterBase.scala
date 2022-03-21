package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.scalatest.funsuite.FixtureAnyFunSuite

import java.io.StringWriter

trait RewriterBase extends FixtureAnyFunSuite {
  protected type FixtureParam = SMTEncoding

  protected var solverContext: SolverContext = _
  protected var arena: Arena = _

  protected def create(rewriterType: SMTEncoding): SymbStateRewriter = {
    rewriterType match {
      case `oopsla19Encoding` => new SymbStateRewriterAuto(solverContext)
      case `arraysEncoding`   => new SymbStateRewriterAutoWithArrays(solverContext)
      case oddRewriterType    => throw new IllegalArgumentException(s"Unexpected rewriter of type $oddRewriterType")
    }
  }

  protected def createWithoutCache(rewriterType: SMTEncoding): SymbStateRewriter = {
    rewriterType match {
      case `oopsla19Encoding` => new SymbStateRewriterImpl(solverContext)
      case `arraysEncoding`   => new SymbStateRewriterImplWithArrays(solverContext)
      case oddRewriterType =>
        throw new IllegalArgumentException(s"Unexpected cacheless rewriter of type $oddRewriterType")
    }
  }

  protected def assertUnsatOrExplain(): Unit = {
    assertOrExplain("UNSAT", !solverContext.sat())
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
    assertUnsatOrExplain()
    rewriter.pop()
    rewriter.pop()
  }

  private def assertOrExplain(msg: String, outcome: Boolean): Unit = {
    if (!outcome) {
      val writer = new StringWriter()
      solverContext.log(writer.getBuffer.toString)
      solverContext.push() // push and pop flush the log output
      solverContext.pop()
      fail("Expected %s, check log.smt for explanation".format(msg))
    }
  }
}
