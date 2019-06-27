package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.{TlaEx, UID}
import javax.inject.Singleton

import at.forsyte.apalache.tla.lir.transformations.TransformationListener

@Singleton
class SourceStoreImpl extends HashMapDB[UID, UID] with TransformationListener {
  // @Igor (08.01.2019): I don't think that we need this rich storage implementation.
  // I would prefer rather having a minimal listener instead. Depending on the application,
  // the user would implement their own efficient storages, e.g., see SourceStore.
  override val m_name : String = "sourceDB"

  override def onTransformation(originEx: TlaEx, newEx: TlaEx): Unit = {
    update(newEx.ID, originEx.ID)
  }

  def traceBack( p_id : UID ) : UID = get( p_id ) match {
    case Some( id ) => traceBack( id )
    case _ => p_id
  }
}

// TODO: Igor (07.01.2019): This object is evil, as it allows one to swallow useful data instead of doing refactoring.
// I have removed most of its usages, and we should just delete this object from the codebase
// TODO: remove
object SourceStoreDummyImpl extends SourceStoreImpl {
  override val m_name : String = "DummySourceDB"

  override def put( key : UID,
                    value : UID
                  ) : Option[UID] = None

  override def update( key : UID,
                       value : UID
                     ) : Unit = {}

  override def get( key : UID ) : Option[UID] = None

  override def size : Int = 0

  override def contains( key : UID ) : Boolean = false

  override def remove( key : UID ) : Unit = {}

  override def clear( ) : Unit = {}

  override def print( ) : Unit = {}

  override def traceBack( p_id : UID ) : UID = p_id

  override def apply( key : UID ) : UID = UID( -1 )

  override def keyCollection : Traversable[UID] = Set.empty[UID]

  /** Retrieves the value associated with the key, if it exists in the database, otherwise returns `elseVal`. */
  override def getOrElse( key : UID,
                          elseVal : UID
                        ) : UID = UID( -1 )
}
