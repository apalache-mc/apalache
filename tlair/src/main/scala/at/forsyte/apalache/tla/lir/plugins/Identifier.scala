package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir.db._
import at.forsyte.apalache.tla.lir._
import java.util.Vector

// REWRITE AS DB[Int, TlaEx]

object UniqueDB extends DB[ UID, TlaEx ] {
  override val name = "UniqueDB"

  private val expressions : Vector[ TlaEx ] = new Vector[ TlaEx ]

  override def apply( key: UID ): Option[ TlaEx ] = {
    if( key.id < 0 || key.id >= expressions.size() ) return None
    else return Some( expressions.elementAt( key.id ) )
  }
  override def size() : Int = expressions.size()

  override def contains( key : UID ) : Boolean = 0 until expressions.size() contains key.id
  override def clear() : Unit = expressions.clear()
  override def print(): Unit = {
    println( "\n" + name + ": \n" )
    for ( i <- 0 until expressions.size()  ) {
      println( UID( i ) + " -> " + expressions.get( i ) )
    }
  }

  def add( ex: TlaEx ) : Unit = {
    if( ex.ID == UID( -1 ) ){
      ex.setID( UID( expressions.size() ) )
      expressions.add( ex )
    }
  }

}


/**
  * Created by jkukovec on 11/28/16.
  */
package object Identifier {
  def identify( spec : TlaSpec ) : Unit = SpecHandler.sideeffectWithExFun( spec, UniqueDB.add )
  def identify( decl : TlaDecl ) : Unit = SpecHandler.sideeffectOperBody( decl , SpecHandler.sideeffectEx( _, UniqueDB.add ) )
  def identify( ex : TlaEx ) : Unit = SpecHandler.sideeffectEx( ex, UniqueDB.add )
}

package object FirstPass extends Plugin {
  override val name = "FirstPass"
  override val dependencies : List[String] = Nil

  /** Cannot produce errors (?)*/
  override def translate(): Unit = {
    output = input.deepCopy()
    SpecHandler.sideeffectWithExFun( output, UniqueDB.add )
  }

  override def reTranslate( err: PluginError ): Unit = {
    /** Forwards errors */
    throwError = err
  }

}
