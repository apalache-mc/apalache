package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt.{Binding, PureArena}

/**
 * A RewriterScope holds data, which is either a byproduct of rewriting, or required supplementary information.
 *
 * @author
 *   Jure Kukovec
 */
sealed case class RewriterScope(arena: PureArena, binding: Binding)
