package at.forsyte.apalache.io.lir

import scala.collection.mutable.HashMap

/**
 * Maps names of variables to more readable strings. Variable names need to be valid TLA variable names, while the
 * readable strings do not have such restrictions.
 * @param writer
 *   a print writer to use
 * @author
 *   Philip Offtermatt
 */
package object NameReplacementMap {
  var nameReplacementMap = new HashMap[String, String]()
}
