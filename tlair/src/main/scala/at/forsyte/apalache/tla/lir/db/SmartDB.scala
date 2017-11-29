package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.{UID, EID}
import collection.mutable.HashMap

/**
  * Basic database, storing a ValType for each KeyType.
  *
  * Provides an interface for data retrieval, but each subclass must implement storage on its own.
  */
abstract class DB[ KeyType, ValType ] {
  val name: String

  /** Retrieves the value associated with the key, if it exists in the database. */
  def apply( key: KeyType ) : Option[ ValType ]
  /** Returns the database size. */
  def size() : Int
  /** Checks whether the key exists in the database. */
  def contains( key : KeyType ) : Boolean
  /** Removes all entries from the database. */
  def clear() : Unit
  /** Debugging method, prints contents to std. output. */
  def print(): Unit
}

/**
  * Basic implementation of a DB wrapping a HashMap.
  */
abstract class HashMapDB[ KeyType, ValType ] extends DB[ KeyType, ValType ] {
  protected val map : HashMap[ KeyType, ValType ] = HashMap()
  def put( key: KeyType, value: ValType ) : Option[ValType] = {
    map.put( key, value )
  }
  def update( key: KeyType, value : ValType ) : Unit = {
    map.update( key, value )
  }
  override def apply( key: KeyType ) : Option[ ValType ] = {
    return map.get( key )
  }
  override def size() : Int = {
    return map.size
  }
  override def contains( key: KeyType ) : Boolean = {
    return map.contains( key )
  }
  def remove( key: KeyType ) : Unit = {
    map.remove( key )
  }
  override def clear() : Unit = {
    map.clear()
  }
  override def print(): Unit = {
    println( "\n" + name + ": \n" )
    for ( ( k, v ) <- map ) {
      println( k + " -> " + v )
    }
  }
}


/**
  * A subclass of DB, which automatically calculates and stores the value associated with a given key.
  *
  * Emulates function memoization.
  */
abstract class SmartDB[ KeyType, ValType ] extends DB[ KeyType, ValType ] {

  /** Lookup that does not compute and store */
  def get( key: KeyType ) : Option[ ValType ]

  /** Computes the value of key, but does not store it */
  def evaluate( key : KeyType ) : Option[ ValType ]

  /**
    * Computes the value of the key and stores it.
    *
    * The method is protected, use apply() as entry point.
    */
  protected def evaluateAndSave( key: KeyType ) : Option[ ValType ]

  /** Lookup that computes and stores the value if it is not already stored */
  override def apply( key: KeyType ) : Option[ ValType ] =  {
    val existing = get( key )
    /** If the key's value has already been calculated, return it. */
    if ( existing.nonEmpty ) {
      return existing
    }
    /** Otherwise, evaluate and store. */
    else{
      return evaluateAndSave( key )
    }
  }
}

abstract class SmartHashMapDB[ KeyType, ValType ] extends SmartDB[ KeyType, ValType ] {
  protected val map : HashMap[ KeyType, ValType ] = HashMap()

  override def get( key: KeyType ) : Option[ ValType ] = {
    return map.get( key )
  }

  protected def evaluateAndSave( key: KeyType ) : Option[ ValType ] ={
    val ret = evaluate( key )
    ret.foreach( map.put( key, _ ) )
    return ret
  }

  override def size() : Int = {
    return map.size
  }
  override def contains( key: KeyType ) : Boolean = {
    return map.contains( key )
  }
  def remove( key: KeyType ) : Unit = {
    map.remove( key )
  }
  override def clear() : Unit = {
    map.clear()
  }
  override def print(): Unit = {
    println( "\n" + name + ": \n" )
    for ( ( k, v ) <- map ) {
      println( k + " -> " + v )
    }
  }



}


/**
  * Shorthand for common KeyTypes (UID, EID).
  */
abstract class UIDB[ ValType ] extends SmartDB[ UID, ValType ]
abstract class EIDB[ ValType ] extends SmartDB[ EID, ValType ]

