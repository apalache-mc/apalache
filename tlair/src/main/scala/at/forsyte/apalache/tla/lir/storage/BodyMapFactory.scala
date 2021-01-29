package at.forsyte.apalache.tla.lir.storage

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaOperDecl}

import scala.collection.immutable.HashMap

// Igor@02.11.2019: why is it an object, not a class? You even have a constructor here, called newMap.
// TODO: refactor into a class.
// TODO: refactor the map to Map[String, TlaOperDecl], remove unnecessary generalization
object BodyMapFactory {
  def newMap: BodyMap = new HashMap[BodyMapKey,BodyMapVal]

  def makeFromDecl( decl : TlaDecl, initial : BodyMap = newMap ) : BodyMap =
    decl match {
      case decl : TlaOperDecl if !initial.contains( decl.name ) =>
        initial + (decl.name -> decl)
      case _ => initial
    }

  def makeFromDecls( decls : Traversable[TlaDecl], initial : BodyMap = newMap ) : BodyMap =
    decls.foldLeft( initial ) { case (db, decl) => makeFromDecl( decl, db ) }
}
