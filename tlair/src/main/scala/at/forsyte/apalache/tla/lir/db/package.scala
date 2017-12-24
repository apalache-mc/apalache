package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.plugins._

/**
  * Returns a database by name.
  *
  */
package object db {
  // TODO: use Google Guice instead of explicitly creating singletons (Igor)
  def apply( name: String ) : DB[_,_] = {
    name match {
      case "EquivalenceDB" => EquivalenceDB
      case "OperatorDB" => OperatorDB
      case "OriginDB" => OriginDB
      case _ => null
    }


  }

}
