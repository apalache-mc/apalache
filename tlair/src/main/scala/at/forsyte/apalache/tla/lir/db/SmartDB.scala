package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.cleaner.Cleaner.IDType
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.plugins.IDAllocator

import collection.mutable.HashMap

/**
  * Wraps a HashMap, performs some kind of evaluation (subclass-specific) and stores that information
  */
abstract trait SmartDB[ ValType ] {
  val name: String
  protected val dbMap : HashMap[ IDType, ValType ] = HashMap()

  def evaluate( key : IDType ) : Option[ ValType ]

  def apply( key: IDType ) : Option[ ValType ] =  {
    val res = dbMap.get( key )
    // If key exists then just return it
    if ( res != None ) {
      return res
    }
    else{
      // Lazy processing
      return evaluate( key )
    }
  }

  def has( key : IDType ) : Boolean = dbMap.contains( key )

  def remove( key : IDType) : Unit = dbMap.remove( key )
}


