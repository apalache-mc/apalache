package at.forsyte.apalache.tla.lir.storage

import scala.collection.mutable

/**
 * Defnes NameReplacementMaps, which map names of variables to more readable strings. Variable names need to be valid
 * TLA variable names, while the readable strings do not have such restrictions. The NameReplacementMap can be used to
 * write prettier output.
 * @author
 *   Philip Offtermatt
 */
package object NameStorage {
  type NameReplacementMap = mutable.HashMap[String, String]
}
