package at.forsyte.apalache.tla.lir.storage

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaOperDecl}

import scala.collection.immutable.HashMap

object BodyMapFactory {
  def newMap: BodyMap = new HashMap[BodyMapKey,BodyMapVal]

  def makeFromDecl( decl : TlaDecl, initial : BodyMap = newMap ) : BodyMap =
    decl match {
      case decl : TlaOperDecl if !initial.contains( decl.name ) =>
        initial + (decl.name -> (decl.formalParams, decl.body))
      case _ => initial
    }

  def makeFromDecls( decls : Traversable[TlaDecl], initial : BodyMap = newMap ) : BodyMap =
    decls.foldLeft( initial ) { case (db, decl) => makeFromDecl( decl, db ) }
}
