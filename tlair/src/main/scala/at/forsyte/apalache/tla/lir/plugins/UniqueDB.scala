package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.db._

import scala.collection.immutable.Vector

// Deprecated: do not use this class. The identifiers are assigned automatically.
// TODO: remove
object UniqueDB extends DB[ UID, TlaEx ] {
  // TODO: @Igor, let's get rid of a singleton here. Make a class.
  // TODO: On a second thought, we do not need this class at all.
  // We should just assign identifiers automatically and stop collecting all expressions.
  override val m_name = "UniqueDB"

  private var expressions : Vector[ TlaEx ] = Vector[ TlaEx ]()

  override def get( key: UID ): Option[ TlaEx ] = {
    assert(key.id.isValidInt)
    if( key.id < 0 || key.id >= expressions.size ) return None
    else return Some( expressions( key.id.toInt ) )
  }

  override def apply( key : UID ) : TlaEx = {
    assert(key.id.isValidInt)
    expressions( key.id.toInt )
  }

  override def size() : Int = expressions.size

  override def contains( key : UID ) : Boolean = 0 <= key.id && key.id < expressions.size
  override def clear() : Unit = expressions = Vector()
  override def print(): Unit = {
    println( "\n" + m_name + ": \n" )
    for ( i <- 0 until expressions.size  ) {
      println( UID( i ) + " -> " + expressions( i ) )
    }
  }

  def add( ex: TlaEx ) : Unit = {
    if( false ){
    }
  }

  override def keyCollection( ) : Traversable[UID] = {
    // backward compatibility with integer ids
    expressions.indices.map(i => UID(i.toLong)).toSet
  }

}


