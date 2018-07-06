package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.control.LetInOper

/**
  * Created by jkukovec on 12/6/16.
  */

/**
  * MAJOR ISSUE: Jure. 15.1.2018: Spec handlers do not handle LET-IN operators properly,
  * they just ignore the delcarations in LET.
  */

//object ExTreeManipulator{
//  val dummyExFun : TlaEx => TlaEx = { x : TlaEx => x }
//  val dummyExSideeffect : TlaEx => Unit = { _ => }
//  val dummyPost : (TlaEx, TlaEx) => Unit = { _ => }
//  val dummyDeclFun: TlaDecl => TlaDecl = { x : TlaDecl => x}
//
//  def generalBaseRecursive(
//                            p_ex : TlaEx,
//                            p_baseCaseCheck : TlaEx => Boolean,
//                            p_baseCaseFun : TlaEx => TlaEx,
//                            p_recursiveCaseFun : TlaEx => TlaEx,
//                            p_post : (TlaEx, TlaEx) => Unit
//                          ) : TlaEx = {
//    val ret = if ( p_baseCaseCheck( p_ex ) ) {
//      p_baseCaseFun( p_ex )
//    }
//    else {
//      p_recursiveCaseFun( p_ex )
//    }
//    p_post( p_ex, ret )
//    ret
//  }
//
//  def operExRecursive(
//                       p_ex : TlaEx,
//                       p_exFun : TlaEx => TlaEx = dummyExFun,
//                       p_postFun : (TlaEx, TlaEx) => Unit = dummyPost
//                     ) : TlaEx = {
//    val newEx = p_exFun( p_ex )
//    newEx match {
//      case OperEx( oper, args@_* ) =>
//        val newOper =
//          oper match {
//            case op : LetInOper =>
//              new LetInOper(
//                op.defs.map( {
//                  case TlaOperDecl( opName, params, opBody ) =>
//                    TlaOperDecl( opName, params, operExRecursive( opBody, p_exFun, p_postFun ) )
//                } )
//              )
//            case _ => oper
//          }
//        val newargs = args.map( operExRecursive( _, p_exFun, p_postFun ) )
//        if ( oper == newOper && args == newargs ) newEx
//        else {
//          val ret = OperEx( oper, newargs : _* )
//          p_postFun( p_ex, ret )
//          ret
//        }
//      case _ => newEx
//    }
//  }
//
//}

object SpecHandler {

  def dummyExFun( p_ex : TlaEx ) : TlaEx = p_ex
  def dummyExSideeffect( p_ex : TlaEx ) : Unit = {}
  def dummyPost(p_exOld : TlaEx, p_exNew: TlaEx) : Unit = {}
  def dummyDeclFun( p_decl : TlaDecl ) : TlaDecl = p_decl
  def dummyTerminationFun( p_ex : TlaEx ) : Boolean = false


  def recursiveTransform( p_ex: TlaEx,
                          p_earlyTermination: TlaEx => Boolean = dummyTerminationFun,
                          p_transform: TlaEx => TlaEx = dummyExFun,
                          p_postFun: (TlaEx, TlaEx) => Unit = dummyPost
                        ): TlaEx = {

    val earlyTermination = p_earlyTermination(p_ex)
    val transformed = p_transform(p_ex)
    val ret =
      if (earlyTermination) transformed
      else transformed match {
        case OperEx( oper, args@_* ) =>
          val newargs = args.map( recursiveTransform( _, p_earlyTermination, p_transform, p_postFun ) )
          if ( args == newargs ) transformed
          else OperEx( oper, newargs : _* )
        case _ => transformed
      }
    p_postFun( p_ex, ret )
    ret
  }

  def getNewEx( p_ex : TlaEx,
                p_exFun : TlaEx => TlaEx = dummyExFun,
                p_postFun : (TlaEx, TlaEx) => Unit = dummyPost
              ) : TlaEx = {
    val newEx = p_exFun( p_ex )
    val ret = newEx match {
      case OperEx( oper, args@_* ) =>
        val newargs = args.map( getNewEx( _, p_exFun, p_postFun ) )
        if ( args == newargs ) newEx
        else OperEx( oper, newargs : _* )
      case _ => newEx
    }
    p_postFun( p_ex, ret )
    ret
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
    p_decl match {
      case TlaOperDecl( _, _, body ) => p_bodyFun( body )
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
                       p_exPostFun : (TlaEx, TlaEx) => Unit = { ( _, _ ) => },
                       p_postBodySideeffect : TlaEx => Unit = { _ => }
                     ) : TlaSpec = {
    getNewDecl( p_spec, getNewOperBody( _, getNewEx( _, p_exFun, p_exPostFun ), p_postBodySideeffect ) )
  }

  def sideeffectWithExFun( p_spec : TlaSpec,
                           p_exFun : TlaEx => Unit = { _ => }
                         ) : Unit = {
    sideeffectDecl( p_spec, sideeffectOperBody( _, sideeffectEx( _, p_exFun ) ) )
  }

  def bottomUpVal[ValType]( p_ex : TlaEx,
                            p_leafJudge : TlaEx => Boolean,
                            p_leafFun : TlaEx => ValType,
                            p_parentFun : (TlaEx, Seq[ValType]) => ValType,
                            p_defalult : ValType
                          ) : ValType = {
    if ( p_leafJudge( p_ex ) )
      p_leafFun( p_ex )
    else
      p_ex match {
        case OperEx( _, args@_* ) =>
          val childVals = args.map( bottomUpVal( _, p_leafJudge, p_leafFun, p_parentFun, p_defalult ) )
          p_parentFun( p_ex, childVals )
        case _ => p_defalult
      }
  }

}
