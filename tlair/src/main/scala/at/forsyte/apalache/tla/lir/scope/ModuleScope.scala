package at.forsyte.apalache.tla.lir.scope

/**
 * A module is just an hierarchical scope.
 */
class ModuleScope(val name: String, val imported: Seq[ModuleScope]) extends ScopeStack {
  for (m <- imported) {
    push(m)
  }
  push(new FlatScope)
}
