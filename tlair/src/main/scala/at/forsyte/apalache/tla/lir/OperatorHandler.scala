package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.db.HashMapDB
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.plugins.Identifier

object OperatorHandler {

  class bodyDB extends HashMapDB[String, (List[FormalParam], TlaEx)] {
    override val name = "bodyDB"

    override def put( key : String, value : (List[FormalParam], TlaEx) ) : Unit = {
      map.put( key, (value._1, value._2.deepCopy( identified = false )) )
    }

    def params( p_name : String ) : Option[List[FormalParam]] = apply( p_name ).map( _._1 )

    def body( p_name : String ) : Option[TlaEx] = apply( p_name ).map( _._2 )

    def arity( p_name : String ) : Option[Integer] = params( p_name ).map( _.size )
  }
  implicit object implBodyDB extends bodyDB

  class sourceDB extends HashMapDB[UID, UID] {
    override val name : String = "sourceDB"

    override def put( key : UID,
                      value : UID
                    ) : Unit =
      (key, value) match {
        case (UID( x ), UID( y )) if x < 0 || y < 0 => /* return */
        case _ => super.put( key, value )
      }
  }

  implicit object implSrcDB extends sourceDB

  def extractOper( p_decl : TlaDecl )
                 ( implicit db : bodyDB ) : Unit = {
    Identifier.identify( p_decl )
    p_decl match {
      case decl : TlaOperDecl => {
        db.put( decl.name, (decl.formalParams, decl.body) )
      }
    }
  }

  def extract( p_spec: TlaSpec ) : Unit = SpecHandler.sideeffectDecl( p_spec, extractOper )

  def replaceAll( p_tlaEx : TlaEx,
                  p_replacedEx: TlaEx,
                  p_newEx: TlaEx
                )
                ( implicit srcDB: sourceDB
                ) : TlaEx = {
    def swap( arg: TlaEx) : TlaEx =
      if ( arg == p_replacedEx ) {
        val ret = p_newEx.deepCopy( identified = false )
        Identifier.identify(ret)
        srcDB.put( ret.ID, arg.ID )
        return ret
      }
      else return arg

    val ret = SpecHandler.getNewEx( p_tlaEx, swap )
    ret
  }

  def unfoldOnce( p_ex : TlaEx )
                ( implicit bdDB : bodyDB,
                  srcDB : sourceDB
                ) : TlaEx = {

    def subAndID( p_operEx : TlaEx ) : TlaEx = {

      def lambda( name: String, args: TlaEx* ) : TlaEx = {
        val pbPair = bdDB( name )
        if (pbPair.isEmpty) return p_operEx
        /** by construction, params.size == args.size */
        var (params, body) = pbPair.get

        params.zip(args).foreach(
          pair => body = replaceAll( body, NameEx( pair._1.name ), pair._2)(srcDB)
        )
        Identifier.identify( body )
        srcDB.put(body.ID, p_operEx.ID)
        /* return */ body
      }

      p_operEx match {
        case OperEx( op: TlaUserOper, args@_* ) => lambda( op.name, args:_* )
        case OperEx( TlaOper.apply, NameEx( name ), args@_* ) => lambda( name, args:_* )
        case _ => p_operEx
      }
    }

    SpecHandler.getNewEx( p_ex, subAndID )
  }

  def unfoldMax( p_ex : TlaEx )
               ( implicit bdDB : bodyDB,
                 srcDB : sourceDB
               ) : TlaEx = {
    var a = p_ex
    var b = unfoldOnce( p_ex )
    while( a != b ){
      a = b
      b = unfoldOnce( b )
    }
    b
  }

}
