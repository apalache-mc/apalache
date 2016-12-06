package at.forsyte.apalache.tla.lir.db

import java.util

import at.forsyte.apalache.tla.lir.plugins.{IDAllocator, Identifier}
import at.forsyte.apalache.tla.lir._
import java.util.Vector

import scala.collection.immutable.Set

case class EID( id : Int ) extends IDType

/**
  * Created by jkukovec on 12/2/16.
  */
class EquivalenceDB extends SmartDB[ EID ]{
  override val name = "EquivalenceDB"

  private val eqClasses : Vector[ Set[ UID ] ] = new Vector[ Set[ UID ] ]()

  private val allocator : IDAllocator[ TlaEx ] = new IDAllocator[ TlaEx ]

  private def allocateEID( ex: TlaEx ) : Unit = allocator.allocate( ex )

  def nKeys() : Int = allocator.nextID()

  private def assignID( ex : TlaEx ) : Unit = {
    apply( ex.ID )

  }

  override def evaluate( key: UID ): Option[ EID ] = {

    def subroutine( ex: TlaEx  ) : Int = {
      SpecHandler.handleEx( ex, allocateEID )
      allocator.getID( ex )
    }
    Identifier.getEx( key ).map( ex => EID( subroutine( ex ) ) )
  }

  def processAll( spec : TlaSpec ) : TlaSpec = SpecHandler.handleWithExFun( spec, assignID )

  def areEquiv( k1 : UID, k2: UID ) : Boolean = this( k1 ) == this( k2 )


}
