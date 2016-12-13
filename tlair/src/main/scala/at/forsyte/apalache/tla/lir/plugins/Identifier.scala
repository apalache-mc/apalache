package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir._
import java.util.Vector


// REWRITE AS DB[Int, TlaEx]

/**
  * Created by jkukovec on 11/28/16.
  */
package object Identifier {

  private val expressions : Vector[TlaEx] = new Vector[TlaEx]

  def reset() : Unit = expressions.clear()

  def getEx( uid : UID ) : Option[TlaEx] = {
    val x = uid.id
    if( x< 0 || x >= expressions.size() )
      return None
    else
      return Some( expressions.get( x ) )
  }

  def size() : Int = expressions.size()

  private def assignID( ex: TlaEx ) : Unit = {
    ex.ID = UID( expressions.size() )
    expressions.add( ex )
  }

  def identify( spec : TlaSpec ) : TlaSpec = SpecHandler.handleWithFun( spec, assignID )
  def identify( decl : TlaDecl ) : TlaDecl = SpecHandler.handleOperBody( decl , SpecHandler.handleEx( _, assignID ) )
  def identify( ex : TlaEx ) : TlaEx = SpecHandler.handleEx( ex, assignID )


}
