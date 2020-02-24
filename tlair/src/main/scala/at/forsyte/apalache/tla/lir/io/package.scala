package at.forsyte.apalache.tla.lir

package object io {
  type NotInvariant = TlaEx
  type State = Map[String, TlaEx]
  type Transition = String
  type NextState = (Transition, State)
}

