package at.forsyte.apalache.tla.bmcmt

import scala.collection.immutable.HashMap

/**
  * Binding variables to memory cells. We keep the number of methods to minimum. If you need all the Map methods,
  * use toMap and convert the result with Binding(...).
  */
class Binding(val toMap: Map[String, ArenaCell]) extends Serializable {
  def apply(name: String): ArenaCell = {
    toMap(name)
  }

  def ++(other: Binding): Binding = {
    new Binding(this.toMap ++ other.toMap)
  }

  def contains(name: String): Boolean = {
    toMap.contains(name)
  }

  // remove non-primed variables and rename primed variables to non-primed
  def shiftBinding(constants: Set[String]): Binding = {
    Binding(forgetNonPrimed(constants).
      toMap.map(p => (p._1.stripSuffix("'"), p._2)))
  }

  // remove primed variables
  def forgetPrimed: Binding = {
    Binding(toMap.filter(p => !p._1.endsWith("'")))
  }

  // remove non-primed variables, except the provided constants
  def forgetNonPrimed(constants: Set[String]): Binding = {
    Binding(toMap.filter(p => p._1.endsWith("'") || constants.contains(p._1)))
  }
}

// a handy companion object
object Binding {
  def apply(): Binding = {
    new Binding(Map.empty)
  }

  def apply(args: (String, ArenaCell)*): Binding = {
    new Binding(HashMap[String, ArenaCell](args :_*))
  }

  def apply(map: Map[String, ArenaCell]): Binding = {
    new Binding(HashMap(map.toSeq :_*))
  }
}

