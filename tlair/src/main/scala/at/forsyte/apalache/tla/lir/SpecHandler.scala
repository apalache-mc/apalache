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
                      bodyFun : TlaEx => TlaEx
                    ) : TlaDecl = {
    decl match{
      case TlaOperDecl( name, params, body ) => {
        return TlaOperDecl( name, params, bodyFun( body ) )
      }
      case _ =>
    }
    return decl
  }

  def handleDecl( spec: TlaSpec, declFun : TlaDecl => TlaDecl ) : TlaSpec = {
    spec.declarations.map( declFun )
    return spec
  }

  def handleWithExFun( spec : TlaSpec,
                       exFun : TlaEx => Unit = { _ => }
                     ) : TlaSpec = {
    return handleDecl( spec, handleOperBody( _, handleEx( _, exFun ) ) )
  }

  def handleWithOperDeclFun( spec : TlaSpec,
                             declFun : TlaOperDecl => TlaOperDecl
                           ) : TlaSpec = {
    return handleDecl( spec, (x : TlaDecl) => x match {
      case TlaOperDecl( _, _, _ ) => declFun( x.asInstanceOf[TlaOperDecl] )
      case _ => x
    })

  }

}
