package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * @author
 *   Jure Kukovec
 */
package object tracee {
  type State = Map[String, TlaEx]
  type StateSeq = IndexedSeq[State]
}
