package at.forsyte.apalache.tla.lir.plugins

import scala.collection.immutable.Vector

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.db._

object UniqueDB extends DB[ UID, TlaEx ] {
  // Igor: let's get rid of a singleton here. Make a class.
  override val m_name = "UniqueDB"

  private var expressions : Vector[ TlaEx ] = Vector[ TlaEx ]()

  override def get( key: UID ): Option[ TlaEx ] = {
    if( key.id < 0 || key.id >= expressions.size ) return None
    else return Some( expressions( key.id ) )
  }

  override def apply( key : UID ) : TlaEx = expressions( key.id )
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

  override def keySet( ) : Set[UID] = expressions.indices.map(UID).toSet

}

class UIDMap extends DB[ UID, TlaEx ] {
  override val m_name = "UIDMap"

  private var m_contents : Vector[ TlaEx ] = Vector[ TlaEx ]()

  override def apply( key : UID ) : TlaEx = m_contents( key.id )
  override def get( key : UID ) : Option[TlaEx] =
    if( !contains( key ) ) None
    else Some( m_contents( key.id ) )

  def add( ex: TlaEx ) : Unit = {
    if( !ex.ID.valid ){
      ex.setID( UID( m_contents.size ) )
      m_contents :+=  ex
    }
  }

  override def clear() : Unit = m_contents = Vector[ TlaEx ]()

  override def print(): Unit = {
    println( "\n" + m_name + ": \n" )
    for ( i <- m_contents.indices  ) {
      println( UID( i ) + " -> " + m_contents( i ) )
    }
  }
  override def contains( key : UID ) : Boolean = key.id < m_contents.size && key.id >= 0

  override def size( ) : Int = m_contents.size

  override def keySet( ) : Set[UID] = m_contents.indices.map( UID ).toSet

}

class UIDHandler {
  private val uidMap = new UIDMap()

  def identify( spec : TlaSpec ) : Unit =
    SpecHandler.sideeffectWithExFun( spec, uidMap.add )
  def identify( decl : TlaDecl ) : Unit =
    SpecHandler.sideeffectOperBody( decl , SpecHandler.sideeffectEx( _, uidMap.add ) )
  def identify( ex : TlaEx ) : Unit =
    SpecHandler.sideeffectEx( ex, uidMap.add )
}

/**
  * Created by jkukovec on 11/28/16.
  */
package object Identifier {
  def identify( spec : TlaSpec ) : Unit = SpecHandler.sideeffectWithExFun( spec, UniqueDB.add )
  def identify( decl : TlaDecl ) : Unit = SpecHandler.sideeffectOperBody( decl , SpecHandler.sideeffectEx( _, UniqueDB.add ) )
  def identify( ex : TlaEx ) : Unit = SpecHandler.sideeffectEx( ex, UniqueDB.add )
}

