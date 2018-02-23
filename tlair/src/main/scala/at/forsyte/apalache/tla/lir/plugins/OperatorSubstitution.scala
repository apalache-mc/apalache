package at.forsyte.apalache.tla.lir.plugins

/**
  * Created by jkukovec on 12/2/16.
  */
import at.forsyte.apalache.tla.lir.db._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._


object OperatorDB extends HashMapDB[ EID, ( List[FormalParam], EID ) ]{
  override val m_name = "OperatorDB"

  def params( eid: EID ) : Option[ List[ FormalParam ] ] =  get( eid ).map( _._1 )

  def arity( eid: EID ) : Option[ Integer ] = params( eid ).map( _.size )

  def body( eid: EID ) : Option[ TlaEx ] =
    get( eid ).map(
      x => EquivalenceDB.getEx( x._2 ).map( _.deepCopy( identified = false ) )
    ).getOrElse( None )


  def isRecursive( eid: EID ): Option[ Boolean ] = {
    val opName = EquivalenceDB.getEx( eid ) match {
      case Some( NameEx( name ) )=> name
      case _ => return None
    }

    var recursive : Boolean = false
    def checkForSelf( tlaEx: TlaEx ) : Unit ={
      tlaEx match{
        case NameEx( name ) => if( name == opName ) recursive = true
        case _ =>
      }
    }
    return body( eid ).map(
      { x => SpecHandler.sideeffectEx( x, checkForSelf ); recursive }
    )

  }

}

object OriginDB extends HashMapDB[ UID, UID ] {
  override val m_name = "OriginDB"
}


package object OperatorSubstitution {

  def extractOper( tlaOperDecl: TlaDecl ) : Unit = {
    if( ! tlaOperDecl.isInstanceOf[TlaOperDecl] ) return
    val thisDecl = tlaOperDecl.asInstanceOf[TlaOperDecl]
    val params = thisDecl.formalParams

    val nameEx = NameEx( thisDecl.name )
    // Give separate UID so EID can be created if operator is never called in other code
    Identifier.identify( nameEx ) // NameEx is lost, do nor re-set multiple times
    val nameEID = EquivalenceDB.get( nameEx )

    // Body needs valid UID

    val bodyEID = EquivalenceDB.get( thisDecl.body )

    if( nameEID.nonEmpty && bodyEID.nonEmpty ) {
      OperatorDB.update( nameEID.get, (params, bodyEID.get) )
    }
  }

  def extract( spec: TlaSpec ) : Unit = SpecHandler.sideeffectDecl( spec, extractOper )

  protected def replaceAll( tlaEx : TlaEx, replacedEx: TlaEx, newEx: TlaEx) : TlaEx = {
    def swap( arg: TlaEx) : TlaEx =
      if ( arg == replacedEx ) {
        return newEx.deepCopy( identified = false )
      }
      else return arg.deepCopy()

    return SpecHandler.getNewEx( tlaEx, swap )
  }

  class ArityMismatch extends Exception

  protected def applyReplace( tlaEx: TlaEx ) : TlaEx = {
    def getBodyOrSelf( ex: TlaEx ) =
      OperatorDB.body( EquivalenceDB.getRaw( ex ) ).getOrElse( ex )
    tlaEx match {
      case NameEx( _ ) => {
        return getBodyOrSelf( tlaEx )
      }
      case OperEx( TlaOper.apply, oper, args@_* ) => {
        val mapval = OperatorDB.get( EquivalenceDB.getRaw( oper ) )
        if (mapval.isEmpty) return tlaEx
        var body = EquivalenceDB.getEx( mapval.get._2 ).get
        val params = mapval.get._1
        if( params.size != args.size ){
          throw new ArityMismatch // arity mismatch
        }
        else{
          params.zip(args).foreach(
            pair => body = replaceAll( body, NameEx( pair._1.name ), pair._2 )
          )
          Identifier.identify( body )
          OriginDB.update(body.ID, tlaEx.ID)
          return body
        }
      }
      case _ => return tlaEx
    }

  }

  // Non- recursive assumed
  def substituteOper( spec: TlaSpec ) : TlaSpec = {
    val retspc = SpecHandler.getNewWithExFun( spec.deepCopy(), applyReplace )
    Identifier.identify( retspc )
    return retspc
  }
}

