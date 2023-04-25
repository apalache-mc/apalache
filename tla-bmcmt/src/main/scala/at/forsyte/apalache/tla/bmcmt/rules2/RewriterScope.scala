package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt.{Binding, PureArena}

/**
 * @author
 *   Jure Kukovec
 */
sealed case class RewriterScope(arena: PureArena, binding: Binding)
