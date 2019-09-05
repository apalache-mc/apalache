package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.{FormalParam, TlaModule, TlaOperDecl}

object SymbolicTransitionInserter {
  def apply( module : TlaModule, transitionOperName : String, transitions : Seq[SymbTrans] ) : TlaModule = {
    val transitionDecls = transitions.zipWithIndex map { case (t, i) =>
      // Name + $ + index is guaranteed to not clash with existing names, as
      // $ is not an allowed symbol in TLA

      // drop selections because of lacking implementation further on
      TlaOperDecl( s"$transitionOperName$$$i", List.empty[FormalParam], t._2 )
    }
    new TlaModule( module.name, module.imports, transitionDecls ++ module.declarations )
  }
}
