package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.db.HashMapDB
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.plugins.{Identifier, UniqueDB}

class BodyDB extends HashMapDB[String, (List[FormalParam], TlaEx)] {
  override val name = "bodyDB"

  override def put( key : String, value : (List[FormalParam], TlaEx) ) : Unit = {
    map.put( key, (value._1, value._2.deepCopy( identified = false )) )
  }

  def params( p_name : String ) : Option[List[FormalParam]] = apply( p_name ).map( _._1 )

  def body( p_name : String ) : Option[TlaEx] = apply( p_name ).map( _._2 )

  def arity( p_name : String ) : Option[Integer] = params( p_name ).map( _.size )
}

class SourceDB extends HashMapDB[UID, UID] {
  override val name : String = "sourceDB"

  override def put( key : UID,
                    value : UID
                  ) : Unit =
    (key, value) match {
      case (UID( x ), UID( y )) if x < 0 || y < 0 => /* return */
      case _ => super.put( key, value )
    }
}

object DummySrcDB extends SourceDB {
  override val name : String = "DummySource"

  override def put( key : UID, value : UID ) : Unit = {}

  override def apply( key : UID ) : Option[UID] = None

  override def size( ) : Int = 0

  override def contains( key : UID ) : Boolean = false

  override def remove( key : UID ) : Unit = {}

  override def clear( ) : Unit = {}

  override def print( ) : Unit = {}
}

object OperatorHandler {

  protected def markSrc( p_old : TlaEx,
                         p_new : TlaEx,
                         p_srcDB : SourceDB
                       ) : Unit = {
    Identifier.identify( p_new )
    if ( p_old.ID != p_new.ID ) {
      p_srcDB.put( p_new.ID, p_old.ID )
    }
  }

  def extractOper( p_decl : TlaDecl,
                     p_db : BodyDB
                   ) : Unit = {
    p_decl match {
      case decl : TlaOperDecl => {
        Identifier.identify( p_decl )
        p_db.put( decl.name, (decl.formalParams, decl.body) )
      }
    }
  }

  def extract( p_spec: TlaSpec,
               p_db: BodyDB
             ) : Unit = SpecHandler.sideeffectDecl( p_spec, extractOper( _, p_db ) )

  def replaceAll( p_tlaEx : TlaEx,
                  p_replacedEx: TlaEx,
                  p_newEx: TlaEx,
                  p_srcDB: SourceDB = DummySrcDB
                ) : TlaEx = {
    def swap( arg : TlaEx ) : TlaEx =
      if ( arg == p_replacedEx ) {
        val ret = p_newEx.deepCopy( identified = false )
        Identifier.identify( ret )
        p_srcDB.put( ret.ID, arg.ID )
        ret
      }
      else arg

    SpecHandler.getNewEx( p_tlaEx, swap, markSrc(_,_,p_srcDB) )
  }

  def replaceWithRule( p_ex : TlaEx,
                       p_rule : TlaEx => TlaEx,
                       p_srcDB : SourceDB = DummySrcDB
                     ) : TlaEx = {
    SpecHandler.getNewEx( p_ex, p_rule, markSrc( _, _, p_srcDB ) )
  }

  def undoReplace( p_ex : TlaEx,
                   p_srcDB : SourceDB
                  ) : TlaEx = {
    if( p_srcDB.contains( p_ex.ID ) ){
      UniqueDB( p_srcDB( p_ex.ID ).get ).get
    }
    else p_ex
  }

  def unfoldOnce( p_ex : TlaEx,
                  p_bdDB : BodyDB,
                  p_srcDB : SourceDB = DummySrcDB
                ) : TlaEx = {

    def subAndID( p_operEx : TlaEx ) : TlaEx = {

      def lambda( name: String, args: TlaEx* ) : TlaEx = {
        val pbPair = p_bdDB( name )
        if (pbPair.isEmpty) return p_operEx
        /** by construction, params.size == args.size */
        var (params, body) = pbPair.get

        params.zip(args).foreach(
          pair => body = replaceAll( body, NameEx( pair._1.name ), pair._2, p_srcDB)
        )
        Identifier.identify( body )
        p_srcDB.put(body.ID, p_operEx.ID)
        /* return */ body
      }

      p_operEx match {
        case OperEx( op: TlaUserOper, args@_* ) => lambda( op.name, args:_* )
        case OperEx( TlaOper.apply, NameEx( name ), args@_* ) => lambda( name, args:_* )
        case _ => p_operEx
      }
    }
    val ret = SpecHandler.getNewEx( p_ex, subAndID )
    Identifier.identify( ret )
    p_srcDB.put( ret.ID, p_ex.ID )
    ret
  }

  def unfoldMax( p_ex : TlaEx,
                 p_bdDB : BodyDB,
                 p_srcDB : SourceDB = DummySrcDB
               ) : TlaEx = {
    var a = p_ex
    var b = unfoldOnce( p_ex, p_bdDB, p_srcDB )
    while( a != b ){
      a = b
      b = unfoldOnce( b, p_bdDB, p_srcDB )
    }
    Identifier.identify( b )
    p_srcDB.put( b.ID, p_ex.ID )
    b
  }

}
