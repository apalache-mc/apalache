package at.forsyte.apalache.tla.lir.storage

import com.google.inject.{Provider, Singleton}
import at.forsyte.apalache.tla.lir.storage.NameReplacementMap
import scala.collection.mutable

/**
 * This class provides us with a singleton factory for a NameReplacementMap. Called via Google Guice.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class NameReplacementMapFactory extends Provider[NameReplacementMap] {
  private val store: NameReplacementMap = new mutable.HashMap[String, String]()

  override def get(): NameReplacementMap = {
    store
  }
}
