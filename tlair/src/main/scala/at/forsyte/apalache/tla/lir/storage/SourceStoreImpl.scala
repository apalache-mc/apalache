package at.forsyte.apalache.tla.lir.storage

import javax.inject.Singleton

import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.{TlaEx, UID}

import scala.collection.mutable

@Singleton
class SourceStoreImpl extends mutable.HashMap[UID, UID] with TransformationListener {
  // @Igor (08.01.2019): I don't think that we need this rich storage implementation.
  // I would prefer rather having a minimal listener instead. Depending on the application,
  // the user would implement their own efficient storages, e.g., see SourceStore.

  override def onTransformation(originEx: TlaEx, newEx: TlaEx): Unit = {
    update(newEx.ID, originEx.ID)
  }

  def traceBack( p_id : UID ) : UID = get( p_id ) match {
    case Some( id ) => traceBack( id )
    case _ => p_id
  }
}
