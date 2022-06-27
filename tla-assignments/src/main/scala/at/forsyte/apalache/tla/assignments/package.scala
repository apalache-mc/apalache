package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.{TlaEx, UID}
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.oper.TlaOper

package object assignments {
  type Var = String
  type StrategyType = Seq[UID]
  type AssignmentType = StrategyType

  type SymbTrans = (AssignmentType, TlaEx)
}
