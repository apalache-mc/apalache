package at.forsyte.apalache.tla.lir.db

import collection.mutable.HashMap

/**
  * Basic database, storing a ValType for each KeyType.
  *
  * Provides an interface for data retrieval, but each subclass must implement storage on its own.
  */
trait DB[KeyType, ValType] {
  val m_name : String

  /** Retrieves the value associated with the key, if it exists in the database. */
  def get( key : KeyType ) : Option[ValType]

  /** Retrieves the value associated with the key, if it exists in the database, otherwise throws. */
  def apply( key : KeyType ) : ValType

  /** Retrieves the value associated with the key, if it exists in the database, otherwise returns `elseVal`. */
  def getOrElse( key : KeyType, elseVal : ValType ) : ValType = get( key ).getOrElse( elseVal )

  /** Returns the database size. */
  def size : Int

  /** Checks whether the key exists in the database. */
  def contains( key : KeyType ) : Boolean

  /** Removes all entries from the database. */
  def clear( ) : Unit

  /** Debugging method, prints contents to std. output. */
  def print( ) : Unit

  def keyCollection : Traversable[KeyType]

  def ==( p_map : Map[KeyType, ValType] ) : Boolean =
    p_map.size == size && p_map.forall( pa => get( pa._1 ).contains( pa._2 ) )
}

/**
  * Basic implementation of a DB wrapping a HashMap.
  */
trait HashMapDB[KeyType, ValType] extends DB[KeyType, ValType] {
  protected val m_map : collection.mutable.HashMap[KeyType, ValType] = collection.mutable.HashMap()

  def put( key : KeyType, value : ValType ) : Option[ValType] = m_map.put( key, value )

  def update( key : KeyType, value : ValType ) : Unit = m_map.update( key, value )

  override def get( key : KeyType ) : Option[ValType] = m_map.get( key )

  override def apply( key : KeyType ) : ValType = m_map( key )

  override def size : Int = m_map.size

  override def contains( key : KeyType ) : Boolean = m_map.contains( key )

  def remove( key : KeyType ) : Unit = m_map.remove( key )

  override def clear( ) : Unit = m_map.clear()

  override def keyCollection : Traversable[KeyType] = m_map.keySet

  override def print( ) : Unit = {
    println( "\n" + m_name + ": \n" )
    m_map foreach { case (k, v) => println( k + " -> " + v ) }
  }
}


/**
  * A subclass of DB, which automatically calculates and stores the value associated with a given key.
  *
  * Emulates function memoization.
  */
trait SmartDB[KeyType, ValType] extends DB[KeyType, ValType] {

  /** Lookup that does not compute and store */
  def peek( key : KeyType ) : Option[ValType]

  /** Computes the value of key, but does not store it */
  def evaluate( key : KeyType ) : Option[ValType]

  /**
    * Computes the value of the key and stores it.
    *
    * The method is protected, use apply() as entry point.
    */
  protected def evaluateAndSave( key : KeyType ) : Option[ValType]

  /** Lookup that computes and stores the value if it is not already stored */
  override def get( key : KeyType ) : Option[ValType] = {
    val existing = peek( key )

    /** If the key's value has already been calculated, return it. */
    if ( existing.nonEmpty )
      existing

    /** Otherwise, evaluate and store. */
    else
      evaluateAndSave( key )
  }
}

trait SmartHashMapDB[KeyType, ValType] extends HashMapDB[KeyType, ValType] with SmartDB[KeyType, ValType] {
  override def peek( key : KeyType ) : Option[ValType] = m_map.get( key )

  override def get( key : KeyType ) : Option[ValType] = super[SmartDB].get( key )

  protected def evaluateAndSave( key : KeyType ) : Option[ValType] = {
    val ret = evaluate( key )
    ret.foreach( m_map.put( key, _ ) )
    ret
  }

}

