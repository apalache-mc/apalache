package at.forsyte.apalache.tla.lir.io

import scala.collection.immutable.HashSet

/**
 * Stores a set of additional variables that were introduced by the temporal encoding. They are stored to exclude these
 * variables enabled rewriting, which should happen only over variables of the original model (since no temporal
 * variables will be mentioned in the expressions).
 * @author
 *   Philip Offtermatt
 */
package object TemporalAuxVarStore {
  var store = new HashSet[String]()
}
