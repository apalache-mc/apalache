package at.forsyte.apalache.tla.lir

/**
  * Created by jkukovec on 12/6/16.
  */

package object SpecHandler {

  def getNewEx( ex : TlaEx, exFun : TlaEx => TlaEx = { x => x } ) : TlaEx = {
    val newEx = exFun( ex )
    if( newEx.isInstanceOf[OperEx] ){
      val oldargs =  newEx.asInstanceOf[OperEx].args
      val newargs = oldargs.map( getNewEx( _ , exFun ) )
      if( newargs == oldargs ) return newEx
      else return OperEx( newEx.asInstanceOf[OperEx].oper, newargs: _*)
    }
    else return newEx
  }

  def sideeffectEx( ex : TlaEx, exFun : TlaEx => Unit = { _ => } ) : Unit = {
    exFun(ex)
    if( ex.isInstanceOf[OperEx] ){
      ex.asInstanceOf[OperEx].args.foreach(
        sideeffectEx( _ , exFun )
      )
    }
  }

  def getNewOperBody( decl : TlaDecl,
                      bodyFun : TlaEx => TlaEx,
                      postBodySideeffect : TlaEx => Unit = { _ => }
                    ) : TlaDecl = {
    decl match{
      case TlaOperDecl( name, params, body ) => {
        val newbody = bodyFun( body )
        if( newbody == body ) return decl
        else {
          postBodySideeffect( newbody )
          return decl.asInstanceOf[TlaOperDecl].copy( body = newbody )
        }
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
    spec.declarations.foreach( declFun )
  }

  def getNewWithExFun( spec : TlaSpec,
                       exFun : TlaEx => TlaEx = { x => x },
                       postBodySideeffect : TlaEx => Unit = { _ => }
                     ) : TlaSpec = {
    return getNewDecl( spec, getNewOperBody( _, getNewEx( _, exFun ), postBodySideeffect ) )
  }

  def sideeffectWithExFun( spec : TlaSpec,
                           exFun : TlaEx => Unit = { _ => }
                         ) : Unit = {
    sideeffectDecl( spec, sideeffectOperBody( _, sideeffectEx( _, exFun ) ) )
  }

}
