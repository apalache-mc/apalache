package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.tla.assignments.SpecWithTransitions

trait SpecWithTransitionsMixin {
  private var specWithTransitions : Option[SpecWithTransitions] = None

  def setSpecWithTransitions( spec : SpecWithTransitions ) : Unit = {
    specWithTransitions = Some( spec )
  }
}
