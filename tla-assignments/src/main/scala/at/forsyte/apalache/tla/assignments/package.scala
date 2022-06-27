package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.{TlaEx, UID}

package object assignments {
  type Var = String
  type StrategyType = Seq[UID]
  type AssignmentType = StrategyType

  type SymbTrans = (AssignmentType, TlaEx)
}
