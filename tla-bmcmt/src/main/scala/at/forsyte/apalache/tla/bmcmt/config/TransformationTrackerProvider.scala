package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.typecheck.integration.TypeWatchdogTransformationListener
import com.google.inject.{Inject, Provider, Singleton}

/**
 * Jure, 4.10.19: This implementation is completely pointless, due to the package architecture.
 * Because the provider uses TrivialTypeFinder, which is defined in `bmcmt`, it cannot be
 * used in all of the passes (e.g. PreproPass), since `pp` cannot have a dependency on `bmcmt`.
 * But because all passes (including PreproPass) require trackers, PreproPassImpl must
 * construct its own tracker anyway.
 */

/**
 * A factory that creates a singleton transformation tracker. The reason for having this factory is that we have
 * to pass a list of transformation listeners to the tracker, while the listeners are injected by Guice.
 *
 * @param changeListener a listener that records which expression was transformed into which expression
 * @author Igor Konnov
 */
@Singleton
class TransformationTrackerProvider @Inject() (changeListener: ChangeListener) extends Provider[TransformationTracker] {

  private val tracker =
    TrackerWithListeners(new TypeWatchdogTransformationListener(), changeListener)

  override def get(): TransformationTracker = {
    tracker
  }
}
