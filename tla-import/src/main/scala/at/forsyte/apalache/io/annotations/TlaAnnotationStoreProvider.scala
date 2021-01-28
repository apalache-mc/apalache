package at.forsyte.apalache.io.annotations

import com.google.inject.{Provider, Singleton}

import at.forsyte.apalache.io.annotations.store._

/**
  * This class provides us with a singleton factory for Google Guice.
  *
  * @author Igor Konnov
  */
@Singleton
class TlaAnnotationStoreProvider extends Provider[TlaAnnotationStore] {
  override def get(): TlaAnnotationStore = {
    createAnnotationStore()
  }
}
