package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.Binding
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.rules.aux.Oracle

/**
 * A symbolic execution that has been translated to SMT.
 *
 * @param arena
 *   an arena that encompasses the cells needed for evaluating the path
 * @param path
 *   the sequence of variables bindings, from the initial state to the final state
 */
class EncodedExecution(val arena: PureArenaAdapter, val path: List[(Binding, Oracle)])

object EncodedExecution {
  def apply(arena: PureArenaAdapter, path: List[(Binding, Oracle)]): EncodedExecution = {
    new EncodedExecution(arena, path)
  }
}
