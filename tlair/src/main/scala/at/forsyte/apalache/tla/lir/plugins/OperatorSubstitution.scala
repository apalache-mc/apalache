package at.forsyte.apalache.tla.lir.plugins

/**
  * Created by jkukovec on 12/2/16.
  */
import at.forsyte.apalache.tla.lir.db.{EquivalenceDB, DB}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._


object OperatorDB extends DB[ EID, Tuple2[ List[FormalParam], EID ] ]{
  override val name = "OperatorDB"

  def arity( eid: EID ) : Option[ Integer ] = apply( eid ).map( _._1.size )

  def body( eid: EID ) : Option[ TlaEx ] =
    apply( eid ).map(
      x => EquivalenceDB.getEx( x._2 )
    ).getOrElse( None )

  def isRecursive( eid: EID ): Option[ Boolean ] = {
    val opName = EquivalenceDB.getEx( eid ) match {
      case Some( NameEx( name ) )=> name
      case _ => return None
    }

    var recursive : Boolean = false
    def checkForSelf( tlaEx: TlaEx ) : Unit ={
      tlaEx match{
        case NameEx( name ) => if( name == opName) recursive = true
        case _ =>
      }
    }
    return body( eid ).map(
      x => SpecHandler.handleEx( x, checkForSelf )
    ).map( _ => recursive)

  }

}

object OriginDB extends DB[ UID, UID ] {
  override val name = "OriginDB"

}


package object OperatorSubstitution {

  private def extractOper( tlaOperDecl: TlaOperDecl ) : TlaOperDecl = {
    val params = tlaOperDecl.formalParams

    val nameEx = NameEx( tlaOperDecl.name )
    // Give separate UID so EID can be created if operator is never called in other code
    Identifier.identify( nameEx ) // NameEx is lost, do nor re-set multiple times
    val nameEID = EquivalenceDB( nameEx.ID )

    val bodyEID = EquivalenceDB( tlaOperDecl.body.ID )

    if( nameEID.nonEmpty && bodyEID.nonEmpty ) {
      OperatorDB.set( nameEID.get, (params, bodyEID.get) )
    }
    return tlaOperDecl
  }

  def extract( spec: TlaSpec ) = SpecHandler.handleWithOperDeclFun( spec, extractOper )


  protected def subEx( tlaEx: TlaEx ) : TlaEx = {
    tlaEx match {
      case OperEx( TlaOper.apply, nameEx, args @ _* ) => {
        val nameEID = EquivalenceDB( nameEx.ID )
      }
      case _ =>
    }

    return  tlaEx
  }

  // Non- recursive assumed
  def substitute( spec: TlaSpec ) : TlaSpec = {

    return spec
  }



}
