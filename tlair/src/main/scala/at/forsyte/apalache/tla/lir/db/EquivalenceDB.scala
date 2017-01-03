package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.plugins.{IDAllocator, Identifier}
import at.forsyte.apalache.tla.lir._
import java.util.Vector
import scala.collection.JavaConversions._

import scala.collection.mutable.Set

class EQDBContainer extends DBContainer[ UID, EID ] {
  private val allocator: IDAllocator[ TlaEx ] = new IDAllocator[ TlaEx ]
  private val eqClasses: Vector[ Set[ UID ] ] = new Vector[ Set[ UID ] ]( )

  @deprecated
  override def put( key: UID, value: EID ): Unit = {
    /** does nothing */
  }

  override def get( key: UID ): Option[ EID ] = {
    Identifier.getEx( key ).map( ( ex: TlaEx ) => EID( allocator.getID( ex ) ) )
  }


  override def size( ): Int = allocator.nextID( )

  override def contains( key: UID ): Boolean = Identifier.getEx( key ).exists( allocator.getID( _ ) != -1 )

  override def remove( key: UID ): Unit = eqClasses.foreach( _.remove( key ) )

  override def clear( ): Unit = allocator.reset()

  override def iterator( ): Iterator[ (UID, EID) ] = {
    ( for ( setI <- 0 until eqClasses.size( );
            uid <- eqClasses.elementAt( setI ) ) yield (uid, get( uid ).get )
    ).iterator
  }
}


/**
  * Keeps track of equivalence classes of TLA expressions. Two expressions are equivalent
  * if they have the exact same form (not value, which is never checked), regardless of unique IDs.
  *
  * Equivalence IDs are introduced to reduce the cost of indexing other databases with TLA expressions.
  */
object EquivalenceDB extends UIDB[ EID ]{
  override val name = "EquivalenceDB"

  private val eqClasses : Vector[ Set[ UID ] ] = new Vector[ Set[ UID ] ]()

  private val allocator : IDAllocator[ TlaEx ] = new IDAllocator[ TlaEx ]

  /**
    * Allocates EID and updates equivalence classes.
    */
  private def allocateEID( ex: TlaEx ) : Unit = {
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
  }

  /**
    * Since the equivalence ID depends only on the form, it can be obtained from any TLA expression.
    * This has the added benefit of being able to deduce the EID of unidentified expressions.
    */
  def getFromEx( tlaEx : TlaEx ) : EID = EID( allocator.getID( tlaEx ) )

  /**
    * Since EIDs and TLA expressions form a one to one correspondence, one can
    * request the original expression from the EID. Note that this method always returns an
    * unidentified copy.
    */
  def getEx( eid : EID ) : Option[TlaEx] = Option( allocator.getVal( eid.id ) ).map( _.deepCopy( identified = false ) )

  override protected def evaluate( key: UID ): Option[ EID ] = {
    /** Allocates IDs to all subexpressions and returns the top expression's EID */
    def subroutine( ex: TlaEx  ) : Int = {
      SpecHandler.sideeffectEx( ex, allocateEID )
      allocator.getID( ex )
    }
    /**
      * Queries the Identifier for the expression corresponding to the provided UID and performs subroutine
      * on it, if it exists. If it does not, a map over None is a no-op and yields None.
      */
    Identifier.getEx( key ).map( ex => EID( subroutine( ex ) ) )
  }

  /**
    * TODO: MOVE TO SEPARATE PLUGIN
    */
  def processAll( spec : TlaSpec ) : Unit = {
    SpecHandler.sideeffectWithExFun( spec, x => apply( x.ID ) )
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
  def getEqClass( key: UID ) : Option[ Set[ UID ] ] = {
    return this( key ).map( getEqClass ).getOrElse(None)
  }

  /**
    * Overload for EID.
    */
  def getEqClass( eid: EID ) : Option[ Set[ UID ] ] = {
    val id = eid.id
    if( id < 0 || id >= eqClasses.size() ) return None
    else return Some( eqClasses.elementAt( id ) )
  }

  /**
    * Overload for TlaEx.
    */
  def getEqClass( tlaEx: TlaEx ) : Option[ Set[ UID ] ] = {
    return getEqClass( getFromEx( tlaEx ) )
  }

  /**
    * Returns the number of allocated EIDs
    */
  def nClasses() : Int = eqClasses.size()

  /**
    * Clears the database. Note that this invalidates all previously allocated EIDs.
    */
  override def clear() = {
    super.clear()
    allocator.reset()
    eqClasses.clear()
  }

}
