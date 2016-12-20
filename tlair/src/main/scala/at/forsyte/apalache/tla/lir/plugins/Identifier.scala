package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir._
import java.util.Vector


// REWRITE AS DB[Int, TlaEx]

/**
  * Created by jkukovec on 11/28/16.
  */
package object Identifier {

  private val expressions : Vector[TlaEx] = new Vector[TlaEx]

  def print() : Unit = {
    println( "\nIdentifier:\n" )
    for ( a <- 0 until expressions.size() ) {
      println( a +  " -> " + expressions.get(a) )
    }
  }


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
    if( ex.ID == UID( -1 ) ){
      ex.setID( UID( expressions.size() ) )
      expressions.add( ex )
    }
  }

  def identify( spec : TlaSpec ) : Unit = SpecHandler.sideeffectWithExFun( spec, assignID )
  def identify( decl : TlaDecl ) : Unit = SpecHandler.sideeffectOperBody( decl , SpecHandler.sideeffectEx( _, assignID ) )
  def identify( ex : TlaEx ) : Unit = SpecHandler.sideeffectEx( ex, assignID )


}
