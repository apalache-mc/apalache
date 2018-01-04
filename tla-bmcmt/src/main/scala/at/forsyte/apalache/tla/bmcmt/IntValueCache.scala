package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}

/**
  * A cache for integer constants that maps an integer to an integer constant in SMT.
  *
  * @author Igor Konnov
  */
class IntValueCache(solverContext: SolverContext) extends AbstractCache[Unit, Int, String] {

  def create(context: Unit, intValue: Int): (Unit, String) = {
    // introduce a new constant
    val intConst = solverContext.introIntConst()
    solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(intConst), ValEx(TlaInt(intValue))))
    (context, intConst)
  }
}
