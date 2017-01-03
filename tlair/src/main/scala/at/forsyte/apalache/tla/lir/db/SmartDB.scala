package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.{UID, EID}
import collection.mutable.HashMap

abstract class DBContainer[KeyType, ValType]{
  def put( key: KeyType, value: ValType ) : Unit
  def get( key: KeyType ) : Option[ValType]
  def size() : Int
  def contains( key: KeyType ) : Boolean
  def remove( key: KeyType ) : Unit
  def clear() : Unit
  def iterator() : Iterator[(KeyType,ValType)]
}

class HashMapWrapper[ KeyType, ValType ] extends DBContainer[ KeyType, ValType ] {
  private val map : HashMap[ KeyType, ValType ] = HashMap()
  def put( key: KeyType, value: ValType ) : Unit = {
    map.put( key, value )
  }
  def get( key: KeyType ) : Option[ValType] = {
    return map.get( key )
  }
  def size() : Int = {
    return map.size
  }
  def contains( key: KeyType ) : Boolean ={
    return map.contains( key )
  }
  def remove( key: KeyType ) : Unit = {
    map.remove( key )
  }
  def clear() : Unit ={
    map.clear()
  }
  def iterator() : Iterator[(KeyType,ValType)] = {
    return map.iterator
  }
}

/**
  * Basic database, storing a ValType for each KeyType.
  *
  * Values must be explicitly set for each key.
  */
abstract class DB[ KeyType,
                   ValType
                 ]( dbContainer : DBContainer[ KeyType, ValType ] =
                    new HashMapWrapper[ KeyType, ValType ]) {
  val name: String
//  protected val dbMap : HashMap[ KeyType, ValType ] = HashMap()

  def put( key: KeyType, value: ValType ) : Unit = dbContainer.put( key, value )

  def apply( key: KeyType ) : Option[ ValType ] = return dbContainer.get( key )

  def size() : Int = dbContainer.size()

  def contains( key : KeyType ) : Boolean = dbContainer.contains( key )

  def remove( key : KeyType) : Unit = dbContainer.remove( key )

  def clear() : Unit = dbContainer.clear()

  def print(): Unit = {
    println( "\n" + name + ": \n" )
    for ( a <- dbContainer.iterator ) {
      println( a._1 + " -> " + a._2 )
    }
  }
}

/**
  * A subclass of DB, which automatically calculates and stores the value associated with a given key.
  *
  * Emulates function memoization.
  */
abstract class SmartDB[ KeyType,
                        ValType
                      ]( dbContainer : DBContainer[ KeyType, ValType ] =
                         new HashMapWrapper[ KeyType, ValType ])
                      extends DB[ KeyType, ValType ](dbContainer) {

  class ValueMismatch(expected: Option[ValType], actual: ValType) extends Exception

  @deprecated
  /**
    * Since SmartDBs calculate their values it is ill-advised to use set explicitly.
    * In particular, the override will calculate its own expected value and compare it with
    * the provided one. If they do not match, a ValueMismatch exception is thrown.
    */
  override def put( key: KeyType, value: ValType ) : Unit = {
    val calculated = evaluate( key )
    /** If calculated value is different from the user value, throw */
    if( calculated.nonEmpty && calculated.get == value) dbContainer.put( key, value )
    else throw new ValueMismatch(calculated, value)

  }

  /** Abstract method to be implemented. */
  protected def evaluate( key : KeyType ) : Option[ ValType ]

  override def apply( key: KeyType ) : Option[ ValType ] =  {
    val res = dbContainer.get( key )
    /**
      * If the key's value has already been calculated, return it.
      */
    if ( res.nonEmpty ) {
      return res
    }
    /**
      * Otherwise, evaluate and store.
      */
    else{
      def lambda( x: ValType ) : ValType = {
        dbContainer.put( key, x )
        return x
      }
      return evaluate( key ).map( lambda )
    }
  }
}

/**
  * Wraps a HashMap, performs some kind of evaluation (subclass-specific) and stores that information
  */
abstract class UIDB[ ValType ]( dbContainer : DBContainer[ UID, ValType ] =
                                new HashMapWrapper[ UID, ValType ])
                              extends SmartDB[ UID, ValType ]
abstract class EIDB[ ValType ] ( dbContainer : DBContainer[ EID, ValType ] =
                                 new HashMapWrapper[ EID, ValType ])
                              extends SmartDB[ EID, ValType ]

