package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.{UID, EID}
import collection.mutable.HashMap

abstract trait DB[ KeyType, ValType ] {
  val name: String
  protected val dbMap : HashMap[ KeyType, ValType ] = HashMap()

  def set( key: KeyType, value: ValType ) : Unit = dbMap.put( key, value )

  def apply( key: KeyType ) : Option[ ValType ] = return dbMap.get( key )

  def size() : Int = dbMap.size

  def has( key : KeyType ) : Boolean = dbMap.contains( key )

  def remove( key : KeyType) : Unit = dbMap.remove( key )

  def reset() : Unit = dbMap.clear()
}
abstract trait SmartDB[ KeyType, ValType ] extends DB[ KeyType, ValType ] {
  protected def evaluate( key : KeyType ) : Option[ ValType ]

  override def apply( key: KeyType ) : Option[ ValType ] =  {
    val res = dbMap.get( key )
    // If key exists then just return it
    if ( res != None ) {
      return res
    }
    else{
      // Lazy processing + saving
      def lambda( x: ValType ) : ValType = {
        dbMap.put( key, x )
        return x
      }
      return evaluate( key ).map( lambda )
    }
  }
}

/**
  * Wraps a HashMap, performs some kind of evaluation (subclass-specific) and stores that information
  */
abstract trait UIDB[ ValType ] extends SmartDB[ UID, ValType ]
abstract trait EIDB[ ValType ] extends SmartDB[ EID, ValType ]

