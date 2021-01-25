package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, Binding}

/**
  * A transition that has been translated to SMT.
  *
  * @param trigger an arena cell that, when asserted, encodes that the transition has fired.
  * @param binding binding of the variables that get assigned by the transition.
  */
class EncodedTransition(val trigger: ArenaCell, val binding: Binding)

object EncodedTransition {
  def apply(trigger: ArenaCell, binding: Binding): EncodedTransition = {
    new EncodedTransition(trigger, binding)
  }
}
