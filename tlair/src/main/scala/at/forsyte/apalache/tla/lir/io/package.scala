package at.forsyte.apalache.tla.lir

package object io {
  type NotInvariant = (String, TlaEx)
  type State = (String, Map[String, TlaEx])
  type Transition = String
  type NextState = (Transition, State)
}

