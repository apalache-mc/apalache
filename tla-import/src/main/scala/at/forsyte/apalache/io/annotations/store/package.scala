package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.tla.lir.UID

import scala.collection.mutable

/**
 * We have to define a package object in its own package, not `at.forsyte.apalache.io.annotations`.
 * Otherwise, scala plugin goes nuts.
 * To get all tha package definitions, import this package as:
 *
 * <pre>at.forsyte.apalache.io.annotations._</pre>
 */
package object store {

  /**
   * A mapping from unique identifiers to annotations, e.g., from operator identifiers to annotations.
   * This mapping is mutable.
   */
  type AnnotationStore = mutable.Map[UID, List[Annotation]]

  /**
   * Create an empty store. Normally, you should not use this method, except in tests.
   * @return a new store
   */
  def createAnnotationStore(): AnnotationStore = {
    new mutable.HashMap[UID, List[Annotation]]()
  }
}
