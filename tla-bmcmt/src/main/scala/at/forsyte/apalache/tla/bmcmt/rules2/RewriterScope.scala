package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt.{Binding, PureArena}

/**
 * A RewriterScope holds data considered mutable during a rewriting execution:
 *   - a PureArena, which holds the subexpression cells and their relations (has, cdm, etc.)
 *   - a Binding, which keeps track of variable names considered bound within the current rewriting scope, and the arena
 *     cells they are represented by. The same expression might be evaluated under different cell bindings to the same
 *     variable name (e.g. in `P` of `\E x \in S: P`).
 *
 * @author
 *   Jure Kukovec
 */
sealed case class RewriterScope(arena: PureArena, binding: Binding)

object RewriterScope {
  def initial(): RewriterScope = RewriterScope(PureArena.initial, Binding())
}
