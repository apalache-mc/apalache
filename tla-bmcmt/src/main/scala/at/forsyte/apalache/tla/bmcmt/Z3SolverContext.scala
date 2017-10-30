package at.forsyte.apalache.tla.bmcmt

import com.microsoft.z3.{BoolExpr, Context, Status}

/**
  * An implementation of a SolverContext with Z3.
  */
class Z3SolverContext extends SolverContext {
  var level: Int = 0
  var numPreds = 2
  val predFalse = "TLB_pred0"
  val predTrue = "TLB_pred1"
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()

  /**
    * Dispose whatever has to be disposed in the end.
    */
  override def dispose(): Unit = {
    z3context.close()
  }

  /**
    * Assert that a given predicate holds
    *
    * @param predName a predicate name
    */
  override def assertPred(predName: String): Unit = {
    z3solver.add(predToBoolExpr(predName))
  }

  /**
    * Introduce a new predicate.
    * @return the name of the new predicate
    */
  override def createPred(): String = {
    val name = "TLB_pred" + numPreds
    numPreds += 1
    z3context.mkBoolConst(name)
    name
  }

  /**
    * Assert than an expression holds.
    * @param expr_s an expression in SMTLIB2
    */
  def assertSmt2(expr_s: String): Unit = {
    z3context.parseSMTLIBString(expr_s, Array(), Array(), Array(), Array())
    z3solver.add(z3context.getSMTLIBFormulas().toSeq: _*)
  }

  override def popTo(newLevel: Int) = {
    level = newLevel
  }

  override def isSat(): Boolean = {
    z3solver.check() == Status.SATISFIABLE
  }

  private def predToBoolExpr(predName: String): BoolExpr = {
    if (predFalse == predName) {
      z3context.mkBool(false)
    } else if (predTrue == predName) {
      z3context.mkBool(true)
    } else {
      z3context.mkBoolConst(predName)
    }
  }
}
