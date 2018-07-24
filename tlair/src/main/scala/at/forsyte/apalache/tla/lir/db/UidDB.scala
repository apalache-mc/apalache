package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.{TlaEx, UID}

import scala.collection.immutable.Vector

class UidDB extends DB[ UID, TlaEx ] {
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
    m_contents foreach { x => println( x.ID + " -> " + x ) }
  }
  override def contains( key : UID ) : Boolean = key.id < m_contents.size && key.id >= 0

  override def size : Int = m_contents.size

  override def keyCollection : Traversable[UID] = m_contents.map( _.ID ).toSet

}