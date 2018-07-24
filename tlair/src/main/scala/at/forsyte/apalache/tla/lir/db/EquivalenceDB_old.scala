package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.plugins._
import at.forsyte.apalache.tla.lir._
import java.util.Vector

import scala.collection.mutable.Set



/**
  * Keeps track of equivalence classes of TLA expressions. Two expressions are equivalent
  * if they have the exact same form (not value, which is never checked), regardless of unique IDs.
  *
  * Equivalence IDs are introduced to reduce the cost of using TLA expressions as pkeys in other databases.
  */
object EquivalenceDB_old extends SmartDB[ TlaEx, EID ]{
  override val m_name = "EquivalenceDB"

  private val eqClasses : Vector[ Set[ UID ] ] = new Vector[ Set[ UID ] ]
  private val allocator : IDAllocator[ TlaEx ] = new IDAllocator[ TlaEx ]

  /** Implicit conversion of -n to None, and n to Some( EID( n ) ) */
  implicit def makeEIDOption( id: Int ) : Option[EID] = {
    if( id < 0 ) return None
    else return Some( EID( id ) )
  }

  /** Retrieves EID from the allocator, WITHOUT allocating anew. Uses implicit conversion */
  override def peek( key: TlaEx ): Option[ EID ] = allocator.getID( key )
  /** Predicts what the EID would be, if allocate were called. Uses implicit conversion */
  override def evaluate( key : TlaEx ) : Option[ EID ] = allocator.predict( key )

  /**
    * Allocates EID and updates equivalence classes.
    */
  protected def evaluateAndSave( ex: TlaEx ) : Option[ EID ] = {
    /** Checks for the next ID, to determine whether a new equivalence class should be created */
    val nStart = allocator.nextID()
    val eid = allocator.allocate( ex )
    /** If the number of allocated IDs remains unchanged, add current element to existing equivalence class */
    if( nStart == allocator.nextID() )
      /** Note: Does nothing if ex.ID is already a member */
      eqClasses.elementAt( eid ).add( ex.ID )
    /** Otherwise create a singleton EC */
    else{
      eqClasses.add( Set[UID]( ex.ID ) )
    }
    return eid
  }

  /** DUMMY */
  override def apply( key : TlaEx ) = EID(-1)

  /** DUMMY */
  override def keyCollection( ) : Traversable[TlaEx] = scala.collection.immutable.Set[TlaEx]()

  /** Returns the number of distinct equivalence IDs assigned. */
  override def size() : Int = allocator.nextID()

  /** Checks if key has an allocated EID. */
  override def contains( key : TlaEx ) : Boolean = allocator.getID( key ) != -1

  /** Prints both the individual EIDs and equivalence classes to std. output. */
  override def print(): Unit = {
    println( "\n" + m_name + ": \n" )
    for ( i <- 0 until allocator.nextID()  ) {
      println( EID( i ) + " -> " + allocator.getVal( i ) )
    }
    println( "\nEquivalence classes: \n" )
    for ( i <- 0 until eqClasses.size()  ) {
      println( EID( i ) + " -> " + eqClasses.elementAt( i ) )
    }
  }


  /**
    * Alternative to get that does not use implicit conversion or Option. Returns
    * EID( -1 ) if not allocated.
    */
  def getRaw( tlaEx : TlaEx ) : EID = EID( allocator.getID( tlaEx ) )

  /**
    * Since EIDs and TLA expressions form a one to one correspondence, one can
    * request the original expression from the EID. Note that this method always returns an
    * unidentified copy.
    */
  def getEx( eid : EID ) : Option[TlaEx] = Option( allocator.getVal( eid.id ) ).map( _.deepCopy( identified = false ) )

  /**
    * TODO: MOVE TO SEPARATE PLUGIN
    */
  def processAll( spec : TlaSpec ) : Unit = {
    SpecHandler.sideeffectWithExFun( spec, evaluateAndSave )
  }

  /**
    * Returns a member from the equivalence class represented by eid, if it exists.
    */
  def getRep( eid: EID ) : Option[ UID ] = {
    return getEqClass( eid ).map( _.head )
  }

  /**
    * Returns the whole equivalence class corresponding to the key, if it exists.
    */
  def getEqClass( eid: EID ) : Option[ Set[ UID ] ] = {
    val id = eid.id
    if( id < 0 || id >= eqClasses.size() ) return None
    else return Some( eqClasses.elementAt( id ) )
  }

  /**
    * Overload for UID.
    */
  def getEqClass( key: UID ) : Option[ Set[ UID ] ] = {
    return UniqueDB.get( key ).map( x => getEqClass( getRaw( x ) ) ).getOrElse(None)
  }

  /**
    * Overload for TlaEx.
    */
  def getEqClass( tlaEx: TlaEx ) : Option[ Set[ UID ] ] = {
    return getEqClass( getRaw( tlaEx ) )
  }

  /**
    * Clears the database. Note that this invalidates all previously allocated EIDs.
    */
  override def clear() = {
    //super.clear()
    allocator.reset()
    eqClasses.clear()
  }

}

