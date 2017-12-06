package at.forsyte.apalache.tla.bmcmt

import org.scalatest.{BeforeAndAfter, FunSuite}

class RewriterBase extends FunSuite with BeforeAndAfter {
  protected var solverContext: SolverContext = new Z3SolverContext()
  protected var arena: Arena = Arena.create(solverContext)

  before {
    solverContext = new Z3SolverContext()
    arena = Arena.create(solverContext)
  }

  after {
    solverContext.dispose()
  }
}
