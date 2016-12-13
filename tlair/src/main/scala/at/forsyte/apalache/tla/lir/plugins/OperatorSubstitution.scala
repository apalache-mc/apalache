package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir.db.{EIDB, SmartDB}
import at.forsyte.apalache.tla.lir._

/**
  * Created by jkukovec on 12/2/16.
  */
import at.forsyte.apalache.tla.lir.db.{EquivalenceDB, DB}
import at.forsyte.apalache.tla.lir.{EID , NameEx, TlaEx}
import at.forsyte.apalache.tla.lir.plugins.{Identifier}


object OperatorDB extends DB[ EID, Tuple2[ List[FormalParam], EID ] ]{
  override val name = "operBodyDB"

  def set( name : String, params: List[FormalParam], body : TlaEx ) : Option[ Tuple3[EID, List[FormalParam], EID]] = {
    val nameEx = NameEx( name )
    // Give separate UID so EID can be created if operator is never called in other code
    Identifier.identify( nameEx )
    val nameEID = EquivalenceDB( nameEx.ID )

    val bodyEID = EquivalenceDB( body.ID )

    if( nameEID.nonEmpty && bodyEID.nonEmpty ) {
      set( nameEID.get, (params, bodyEID.get) )
      return Some( ( nameEID.get, params, bodyEID.get ) )
    }
    else return None
  }




}

package object OperatorSubstitution {

  private def extractOper( decl: TlaDecl ) : TlaDecl = {
    decl match{
      case TlaOperDecl( name, params, body ) => {
        OperatorDB.set( name, params, body )
      }
      case _ =>
    }
    return decl
  }

  def arity( eid: EID ) : Option[ Integer ] = {
    OperatorDB( eid ).map( _._1.size )
  }


  def apply( spec: TlaSpec ) : TlaSpec = {

    return SpecHandler.handleWithFun( spec,
      {_ => }, //e
      {_ => }, // name
      {_ => } // params
    )

    return spec
  }

}
