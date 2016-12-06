package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir.{TlaEx, UID, TlaSpec, SpecHandler}
import java.util.Vector

/**
  * Created by jkukovec on 11/28/16.
  */
package object Identifier {

  private val expressions : Vector[TlaEx] = new Vector[TlaEx]

  def reset() : Unit = {
    expressions.clear()
  }

  def getEx( uid : UID ) : Option[TlaEx] = {
    val x = uid.id
    if( x< 0 || x >= expressions.size() )
      return None
    else
      return Some( expressions.get( x ) )
  }

  def nAllocated() : Int = expressions.size()

  private def assignID( ex: TlaEx ) : Unit = {
    ex.ID = UID( expressions.size() )
    expressions.add( ex )

  }

  def identify( spec : TlaSpec ) = SpecHandler.handleWithExFun( spec, assignID )

}
