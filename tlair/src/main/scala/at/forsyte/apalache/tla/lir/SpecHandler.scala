package at.forsyte.apalache.tla.lir

/**
  * Created by jkukovec on 12/6/16.
  */

object SpecHandler {

  def getNewEx( p_ex : TlaEx,
                p_exFun : TlaEx => TlaEx = { x => x }
              ) : TlaEx = {
    val newEx = p_exFun( p_ex )
    newEx match {
      case OperEx( oper, args@_* ) => {
        val newargs = args.map( getNewEx( _, p_exFun ) )
        if ( args == newargs ) return newEx
        else return OperEx( oper, newargs : _* )
      }
      case _ => newEx
    }
  }

  def sideeffectEx( p_ex : TlaEx,
                    p_exFun : TlaEx => Unit = { _ => }
                  ) : Unit = {
    p_exFun( p_ex )
    p_ex match {
      case OperEx( _, args@_* ) => args.foreach( sideeffectEx( _, p_exFun ) )
      case _ =>
    }
  }

  def getNewOperBody( p_decl : TlaDecl,
                      p_bodyFun : TlaEx => TlaEx,
                      p_postBodySideeffect : TlaEx => Unit = { _ => }
                    ) : TlaDecl = {
    p_decl match {
      case TlaOperDecl( name, params, body ) => {
        val newbody = p_bodyFun( body )
        if ( newbody == body ) p_decl
        else {
          p_postBodySideeffect( newbody )
          TlaOperDecl( name, params, newbody )
        }
      }
      case _ => p_decl
    }
  }

  def sideeffectOperBody( p_decl : TlaDecl,
                          p_bodyFun : TlaEx => Unit
                        ) : Unit = {
    p_decl match{
      case TlaOperDecl(_,_, body) => p_bodyFun( body )
      case _ =>
    }
  }

  def getNewDecl( p_spec : TlaSpec,
                  p_declFun : TlaDecl => TlaDecl = { x => x }
                ) : TlaSpec = {
    p_spec.copy( declarations = p_spec.declarations.map( p_declFun ) )
  }

  def sideeffectDecl( p_spec : TlaSpec,
                      p_declFun : TlaDecl => Unit = { _ => }
                    ) : Unit = {
    p_spec.declarations.foreach( p_declFun )
  }

  def getNewWithExFun( p_spec : TlaSpec,
                       p_exFun : TlaEx => TlaEx = { x => x },
                       p_postBodySideeffect : TlaEx => Unit = { _ => }
                     ) : TlaSpec = {
    getNewDecl( p_spec, getNewOperBody( _, getNewEx( _, p_exFun ), p_postBodySideeffect ) )
  }

  def sideeffectWithExFun( p_spec : TlaSpec,
                           p_exFun : TlaEx => Unit = { _ => }
                         ) : Unit = {
    sideeffectDecl( p_spec, sideeffectOperBody( _, sideeffectEx( _, p_exFun ) ) )
  }

}
