package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.{FormalParam, NullEx, TlaEx}

class BodyDB extends HashMapDB[String, (List[FormalParam], TlaEx)] {
  override val m_name = "bodyDB"

  override def put( key : String,
                    value : (List[FormalParam], TlaEx)
                  ) : Option[(List[FormalParam], TlaEx)] =
    m_map.put( key, (value._1, value._2.deepCopy( identified = false )) )

  override def update( key : String,
                       value : (List[FormalParam], TlaEx)
                     ) : Unit =
    m_map.update( key, (value._1, value._2.deepCopy( identified = false )) )

  def params( p_name : String ) : Option[List[FormalParam]] = get( p_name ).map( _._1 )

  def body( p_name : String ) : Option[TlaEx] = get( p_name ).map( _._2 )

  def arity( p_name : String ) : Option[Integer] = params( p_name ).map( _.size )
}

object DummyBodyDB extends BodyDB {
  override val m_name : String = "DummyBodyDB"

  override def put( key : String,
                    value : (List[FormalParam], TlaEx)
                  ) : Option[(List[FormalParam], TlaEx)] = None

  override def update( key : String,
                       value : (List[FormalParam], TlaEx)
                     ) : Unit = {}

  override def params( p_name : String ) : Option[List[FormalParam]] = None

  override def body( p_name : String ) : Option[TlaEx] = None

  override def arity( p_name : String ) : Option[Integer] = None

  override def get( key : String ) : Option[(List[FormalParam], TlaEx)] = None

  override def apply( key : String ) : (List[FormalParam], TlaEx) = (List(), NullEx)

  override def size : Int = 0

  override def contains( key : String ) : Boolean = false

  override def remove( key : String ) : Unit = {}

  override def clear( ) : Unit = {}

  override def keyCollection : Traversable[String] = Set.empty[String]

  //  override def keyCollection( ) : Traversable[UID] = Set.empty[UID]

  /** Retrieves the value associated with the key, if it exists in the database, otherwise returns `elseVal`. */
  override def getOrElse( key : String,
                          elseVal : (List[FormalParam], TlaEx)
                        ) : (List[FormalParam], TlaEx) = (List(), NullEx)
}
