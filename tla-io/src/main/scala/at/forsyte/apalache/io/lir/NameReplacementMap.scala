package at.forsyte.apalache.io.lir

import scala.collection.mutable.HashMap


/**
 * This class produces counterexamples in the Informal Trace Format.
 *
 * @param writer
 *   a print writer to use
 * @author
 *   Philip Offtermatt
 */
package object NameReplacementMap {
    var NameReplacementMap = new HashMap[String, String]()
}
