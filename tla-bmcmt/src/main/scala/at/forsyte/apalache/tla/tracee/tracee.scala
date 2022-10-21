package at.forsyte.apalache.tla

/**
 * @author
 *   Jure Kukovec
 */
package object tracee {
  type State = at.forsyte.apalache.io.lir.State
  type Trace = IndexedSeq[State]
}
