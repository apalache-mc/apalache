package at.forsyte.apalache.io

import at.forsyte.apalache.tla.lir.TlaEx

package object lir {
  type NotInvariant = TlaEx
  type State = Map[String, TlaEx]
  type Trace = IndexedSeq[State]
  type Transition = String
  type NextState = (Transition, State)
}
