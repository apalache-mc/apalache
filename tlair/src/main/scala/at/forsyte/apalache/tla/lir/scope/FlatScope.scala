package at.forsyte.apalache.tla.lir.scope

import scala.collection.immutable.HashMap

/**
* Created by konnov on 11/15/16.
*/
class FlatScope extends TlaScope {
  var map = HashMap.empty[String, ScopeSymbol]

  override def add(sym: ScopeSymbol) = {
    map = map + ((sym.name, sym))
  }

  override def remove(name: String) = {
    map = map - name
  }

  override def exists(name: String): Boolean = {
    map.contains(name)
  }

  override def lookup(name: String): ScopeSymbol = {
    map.get(name) match {
      case Some(s) => s
      case None => throw new SymbolNotFoundException("Symbol %s not found".format(name))
    }
  }
}
