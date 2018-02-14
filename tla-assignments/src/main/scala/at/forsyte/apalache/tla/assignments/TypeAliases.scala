package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.{TlaEx, UID}

trait TypeAliases {
  type StrategyType = Seq[UID]
  type AssignmentType = StrategyType

  type SymbTrans = (AssignmentType, TlaEx)

}
