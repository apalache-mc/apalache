package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.UID
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.plugins.IDAllocator
import collection.mutable.HashMap

abstract class DB[ KeyType, ValType ] {
  val name: String
  protected val dbMap : HashMap[ KeyType, ValType ] = HashMap()

  protected def evaluate( key : KeyType ) : Option[ ValType ]

  def apply( key: KeyType ) : Option[ ValType ] =  {
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
      evaluate( key ).map( lambda )
    }
  }

  def has( key : KeyType ) : Boolean = dbMap.contains( key )

  def remove( key : KeyType) : Unit = dbMap.remove( key )
}

/**
  * Wraps a HashMap, performs some kind of evaluation (subclass-specific) and stores that information
  */
abstract class SmartDB[ ValType ] extends DB[ UID, ValType ]{

}


