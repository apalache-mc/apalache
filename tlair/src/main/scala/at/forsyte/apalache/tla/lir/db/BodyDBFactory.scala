package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaOperDecl}

object BodyDBFactory {
  def makeDBFromDecl( decl : TlaDecl, initial : BodyDB = new BodyDB ) : BodyDB =
    decl match {
      case decl : TlaOperDecl if !initial.contains( decl.name ) =>
        initial.update( decl.name, (decl.formalParams, decl.body) )
        initial
      case _ => initial
    }

  def makeDBFromDecls( decls : Traversable[TlaDecl], initial : BodyDB = new BodyDB ) : BodyDB =
    decls.foldLeft( initial ) { case (db, decl) => makeDBFromDecl( decl, db ) }
}
