package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.TlaType1
import at.forsyte.apalache.tla.typecheck.etc.{EtcRef, ExactRef}

/**
 * MultiTypeCheckerListener simply broadcasts the events to the listeners that it is initialized with.
 *
 * @param subscribers a sequence of subscribed listeners
 */
class MultiTypeCheckerListener(subscribers: TypeCheckerListener*) extends TypeCheckerListener {
  override def onTypeFound(sourceRef: ExactRef, monotype: TlaType1): Unit = {
    for (s <- subscribers) {
      s.onTypeFound(sourceRef, monotype)
    }
  }

  override def onTypeError(sourceRef: EtcRef, message: String): Unit = {
    for (s <- subscribers) {
      s.onTypeError(sourceRef, message)
    }
  }
}
