package at.forsyte.apalache.tla.lir

/**
  * Created by jkukovec on 12/6/16.
  */

package object SpecHandler {

  def handleEx( ex : TlaEx, exFun : TlaEx => Unit ) : TlaEx = {
    exFun( ex )
    ex match {
      case OperEx( oper, args @ _* ) =>
        args.foreach(
         handleEx( _ , exFun )
        )
      case _ => ex
    }
    return ex
  }

  def handleOperBody( decl : TlaDecl, bodyFun : TlaEx => TlaEx ) : TlaDecl = {
    decl match{
      case TlaOperDecl( _, _, body ) => bodyFun( body )
      case _ => decl
    }
    return decl
  }

  def handleDecl( spec: TlaSpec, declFun : TlaDecl => TlaDecl ) : TlaSpec = {
    spec.declarations.foreach( declFun )
    return spec
  }

  def handleWithExFun( spec : TlaSpec, exFun : TlaEx => Unit ) : TlaSpec = {
    return handleDecl( spec, handleOperBody( _, handleEx( _, exFun ) ) )
  }

}
