package at.forsyte.apalache.tla.lir.io

import scala.collection.mutable.HashMap

/**
 * Maps names of variables to more readable strings.
 * Variable names need to be valid TLA variable names, while the readable strings
 * do not have such restrictions.
 * @author
 *   Philip Offtermatt
 */
package object NameReplacementMap {
  var NameReplacementMap = new HashMap[String, String]()
}
