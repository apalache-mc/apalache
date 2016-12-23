package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.plugins.{IDAllocator, Identifier}
import at.forsyte.apalache.tla.lir._
import java.util.Vector

import scala.collection.mutable.Set

/**
  * Created by jkukovec on 12/2/16.
  */
object EquivalenceDB extends UIDB[ EID ]{
  override val name = "EquivalenceDB"

  private val eqClasses : Vector[ Set[ UID ] ] = new Vector[ Set[ UID ] ]()

  private val allocator : IDAllocator[ TlaEx ] = new IDAllocator[ TlaEx ]

  private def allocateEID( ex: TlaEx ) : Unit = {
    val nStart = allocator.nextID()
    val eid = allocator.allocate( ex )
    if( nStart == allocator.nextID() ) // no new alloc, id exists
      eqClasses.elementAt( eid ).add( ex.ID )
    else{
      eqClasses.add( Set[UID]( ex.ID ) )
    }
  }

  def getFromEx( tlaEx : TlaEx ) : EID = EID( allocator.getID( tlaEx ) )

  /** returns unidentified expression */
  def getEx( eid : EID ) : Option[TlaEx] = Option( allocator.getVal( eid.id ) ).map( _.deepCopy( identified = false ) )

  override protected def evaluate( key: UID ): Option[ EID ] = {

    def subroutine( ex: TlaEx  ) : Int = {
      SpecHandler.sideeffectEx( ex, allocateEID )
      allocator.getID( ex )
    }
    Identifier.getEx( key ).map( ex => EID( subroutine( ex ) ) )
  }

  def processAll( spec : TlaSpec ) : Unit = {
    SpecHandler.sideeffectWithExFun( spec, x => apply( x.ID ) )
  }

  def areEquiv( k1: UID, k2: UID ) : Boolean = this( k1 ) == this( k2 )

  def getRep( eid: EID ) : Option[ UID ] = {
    return getEqClass( eid ).map( _.head )
  }

  def getEqClass( key: UID ) : Option[ Set[ UID ] ] = {
    return this( key ).map( getEqClass ).getOrElse(None)
  }
  def getEqClass( eid: EID ) : Option[ Set[ UID ] ] = {
    val id = eid.id
    if( id < 0 || id >= eqClasses.size() ) return None
    else return Some( eqClasses.elementAt( id ) )
  }
  def getEqClass( tlaEx: TlaEx ) : Option[ Set[ UID ] ] = {
    return getEqClass( getFromEx( tlaEx ) )
  }

  def nClasses() : Int = eqClasses.size()

  override def reset() = {
    super.reset()
    allocator.reset()
    eqClasses.clear()
  }

}
