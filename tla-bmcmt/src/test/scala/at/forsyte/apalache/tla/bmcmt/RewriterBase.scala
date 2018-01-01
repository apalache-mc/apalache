package at.forsyte.apalache.tla.bmcmt

import java.io.{PrintWriter, StringWriter}

import org.scalatest.{BeforeAndAfter, FunSuite}

class RewriterBase extends FunSuite with BeforeAndAfter {
  protected var solverContext: SolverContext = new Z3SolverContext()
  protected var arena: Arena = Arena.create(solverContext)

  before {
    solverContext = new Z3SolverContext(debug = true)
    arena = Arena.create(solverContext)
  }

  after {
    solverContext.dispose()
  }

  protected def assertUnsatOrExplain(state: SymbState): Unit = {
    assertOrExplain("UNSAT", state, !solverContext.sat())
  }

  private def assertOrExplain(msg: String, state: SymbState, outcome: Boolean): Unit = {
    if (!outcome) {
      val writer = new StringWriter()
      new SymbStateDecoder(solverContext).dumpArena(state, new PrintWriter(writer))
      solverContext.log(writer.getBuffer.toString)
      solverContext.push() // push and pop flush the log output
      solverContext.pop()
      fail("Expected %s, check log.smt for explanation".format(msg))
    }

  }
}
