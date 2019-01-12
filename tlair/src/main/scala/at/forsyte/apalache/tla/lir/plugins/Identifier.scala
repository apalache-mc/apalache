package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.db._

import scala.collection.immutable.Vector

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
    if( !ex.ID.valid ){
      ex.setID( UID( expressions.size ) )
      expressions :+=  ex
    }
  }

  override def keyCollection( ) : Traversable[UID] = {
    // backward compatibility with integer ids
    expressions.indices.map(i => UID(i.toLong)).toSet
  }

}

/**
  * Created by jkukovec on 11/28/16.
  */
package object Identifier {
  def identify( spec : TlaSpec ) : TlaSpec = {
    SpecHandler.sideeffectWithExFun( spec, UniqueDB.add )
    spec
  }

  def identify( decl : TlaDecl ) : TlaDecl = {
    SpecHandler.sideeffectOperBody(decl, SpecHandler.sideeffectEx(_, UniqueDB.add))
    decl
  }

  def identify( ex : TlaEx ) : TlaEx = {
    SpecHandler.sideeffectEx( ex, UniqueDB.add )
    ex
  }
}

