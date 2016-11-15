package at.forsyte.apalache.tla.lir.scope

/**
* Created by konnov on 11/15/16.
*/
class ScopeStack extends TlaScope {
  var scopes: List[TlaScope] = List()

  override def add(sym: ScopeSymbol) = {
    scopes.head.add(sym)
  }

  override def remove(name: String) = {
    scopes.find { s => s.exists(name) } match {
      case Some(s) => s.remove(name)
      case None => ()
    }
  }

  override def lookup(name: String) = {
    def search(s: Seq[TlaScope]): ScopeSymbol = {
      s match {
        case Seq() =>
          throw new SymbolNotFoundException("Symbol %s not found".format(name))

        case hd :: tl =>
          try {
            hd.lookup(name)
          } catch {
            case _: SymbolNotFoundException => search(tl)
          }
      }
    }
    search(scopes)
  }

  override def exists(name: String) = {
    try {
      lookup(name)
      true
    } catch {
      case _: SymbolNotFoundException =>
        false
    }
  }

  def push(s: TlaScope) = {
    scopes = s :: scopes
  }

  def pop(): Unit = {
    if (scopes.isEmpty) throw new IllegalStateException("Empty scope stack")
    else scopes = scopes.tail
  }
}
