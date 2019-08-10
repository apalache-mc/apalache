package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import com.google.inject.{Inject, Provider, Singleton}

/**
  * A factory that creates a singleton transformation tracker. The reason for having this factory is that we have
  * to pass a list of transformation listeners to the tracker, while the listeners are injected by Guice.
  *
  * @param sourceStore a source store
  *
  * @author Igor Konnov
  */
@Singleton
class TransformationTrackerProvider @Inject()(sourceStore: SourceStore)
    extends Provider[TransformationTracker] {

  private val tracker = TrackerWithListeners(sourceStore)

  override def get(): TransformationTracker = {
    tracker
  }
}
