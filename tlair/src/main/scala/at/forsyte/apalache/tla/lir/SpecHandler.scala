package at.forsyte.apalache.tla.lir

/**
  * Created by jkukovec on 12/6/16.
  */

package object SpecHandler {

  def getNewEx( ex : TlaEx, exFun : TlaEx => TlaEx = { x => x } ) : TlaEx = {
    if( ex.isInstanceOf[OperEx] ){
      val newargs = ex.asInstanceOf[OperEx].args.map(
        getNewEx( _ , exFun )
      )
      val newEx = OperEx( ex.asInstanceOf[OperEx].oper, newargs: _*)
      newEx.ID = ex.ID
      return exFun( newEx )
    }
    else return exFun(ex)
  }

  def sideeffectEx( ex : TlaEx, exFun : TlaEx => Unit = { _ => } ) : Unit = {
    if( ex.isInstanceOf[OperEx] ){
      ex.asInstanceOf[OperEx].args.map(
        sideeffectEx( _ , exFun )
      )
    }
    exFun(ex)
  }

  def getNewOperBody( decl : TlaDecl,
                      bodyFun : TlaEx => TlaEx
                    ) : TlaDecl = {
    decl match{
      case TlaOperDecl( name, params, body ) => {
        return decl.asInstanceOf[TlaOperDecl].copy( body = bodyFun( body ) )
      }
      case _ => return decl
    }
  }

  def sideeffectOperBody( decl : TlaDecl,
                          bodyFun : TlaEx => Unit
                        ) : Unit = {
    if( decl.isInstanceOf[TlaOperDecl] ) bodyFun( decl.asInstanceOf[TlaOperDecl].body )
  }

  def getNewDecl( spec: TlaSpec, declFun : TlaDecl => TlaDecl ) : TlaSpec = {
    return spec.copy( declarations = spec.declarations.map( declFun ) )
  }

  def sideeffectDecl( spec: TlaSpec, declFun : TlaDecl => Unit ) : Unit = {
    spec.declarations.map( declFun )
  }

  def getNewWithExFun( spec : TlaSpec,
                       exFun : TlaEx => TlaEx = { x => x }
                     ) : TlaSpec = {
    return getNewDecl( spec, getNewOperBody( _, getNewEx( _, exFun ) ) )
  }

  def sideeffectWithExFun( spec : TlaSpec,
                           exFun : TlaEx => Unit = { _ => }
                         ) : Unit = {
    sideeffectDecl( spec, sideeffectOperBody( _, sideeffectEx( _, exFun ) ) )
  }

}
