package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.plugins._

/**
  * Created by jkukovec on 12/22/16.
  */
package object db {
  // Avoid option, too verbose
  def apply( name: String ) : Database = {
    name match {
      case "EquivalenceDB" => EquivalenceDB
      case "OperatorDB" => OperatorDB
      case "OriginDB" => OriginDB
      case _ => null
    }
  }

}
