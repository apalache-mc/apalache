package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.cleaner.Cleaner.IDType
import collection.mutable.HashMap

/**
  * Wraps a HashMap with fixed key type
  */
class Database[ValType](name: String) {
  protected val dbMap : HashMap[IDType, ValType] = HashMap()

  def apply( key: IDType ): Option[ValType] =  dbMap.get( key )

  def remove( key : IDType) : Unit = dbMap.remove(key)

}
