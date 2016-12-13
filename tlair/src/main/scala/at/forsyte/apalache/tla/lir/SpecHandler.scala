package at.forsyte.apalache.tla.lir

/**
  * Created by jkukovec on 12/6/16.
  */

package object SpecHandler {

  def handleEx( ex : TlaEx, exFun : TlaEx => Unit = { _ => } ) : TlaEx = {
    exFun( ex )
    ex match {
      case OperEx( oper, args @ _* ) =>
        args.foreach(
         handleEx( _ , exFun )
        )
      case _ =>
    }
    return ex
  }

  def handleOperBody( decl : TlaDecl,
                      bodyFun : TlaEx => TlaEx,
                      nameFun : String => Unit = { _ => },
                      paramsFun: List[FormalParam] => Unit = { _ => }
                    ) : TlaDecl = {
    decl match{
      case TlaOperDecl( name, params, body ) => {
        nameFun( name )
        paramsFun( params )
        bodyFun( body )
        //return TlaOperDecl( name, params, bodyFun( body ) )
      }
      case _ =>
    }
    return decl
  }

  def handleDecl( spec: TlaSpec, declFun : TlaDecl => TlaDecl ) : TlaSpec = {
    spec.declarations.foreach( declFun )
    return spec
  }

  def handleWithFun( spec : TlaSpec,
                     exFun : TlaEx => Unit = { _ => },
                     nameFun : String => Unit = { _ => },
                     paramsFun: List[FormalParam] => Unit = { _ => }
                     ) : TlaSpec = {
    return handleDecl( spec, handleOperBody( _, handleEx( _, exFun ), nameFun, paramsFun) )
  }

}
