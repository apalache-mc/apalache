package at.forsyte.apalache.tla.lir

// TODO: these are probably handy functions, but they should not be in **.lir
package object stdfun {

  class FilterInvalidationError( p_ex : OperEx ) extends Exception {
    override def getMessage : String =
      "Filtering %s results in incorrect arity of the operator %s".format( p_ex, p_ex.oper.name )
  }

  protected def filterBody( p_ex : TlaEx,
                            p_filterFun : TlaEx => Boolean
                          ) : TlaEx = {
    p_ex match {
      case OperEx( oper, args@_* ) =>
        val newargs = args.withFilter( p_filterFun ).map( filterBody( _, p_filterFun ) ).filter( p_filterFun )
        if ( args == newargs ) p_ex
        else {
          if ( oper.isCorrectArity( newargs.size ) )
            OperEx( oper, newargs : _* )
          else throw new FilterInvalidationError( p_ex.asInstanceOf[OperEx] )
        }
      case _ => p_ex
    }
  }

  def filter( p_ex : TlaEx, p_filterFun : TlaEx => Boolean ) : TlaEx = {

    val ret = filterBody( p_ex, p_filterFun )
    if( p_filterFun( ret ) ) ret
    else NullEx

  }
}
