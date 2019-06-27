package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.control.LetInOper
import at.forsyte.apalache.tla.lir.db.BodyDB
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.transformations.TransformationListener

// TODO: @Igor: please move it to the package *.process
// TODO: This code looks obfuscated: there are way too many lambdas and no comments at all.
object OperatorHandler {

  protected def markSrc(p_old : TlaEx,
                        p_new : TlaEx,
                        p_listener : TransformationListener
                       ) : Unit = {
    if ( p_old.ID != p_new.ID ) {
      p_listener.onTransformation(p_old, p_new)
    }
  }

  protected def pfx( p_prefix : String, p_s : String ) : String = "%s_%s".format( p_prefix, p_s )

  protected def renameParam( p_prefix : String )( p_param : FormalParam ) : FormalParam = {
    p_param match {
      case SimpleFormalParam( name ) => SimpleFormalParam( pfx( p_prefix, name ) )
      case OperFormalParam( name, arity ) => OperFormalParam( pfx( p_prefix, name ), arity )
    }
  }

  /**
    *
    * TODO: Test with proper srcDB
    *
    * @param p_decls
    * @return
    */
  def uniqueVarRename( p_decls : Seq[TlaDecl], p_srcDB : TransformationListener) : Seq[TlaDecl] = {
    def lambda( p_boundVars : Set[String], p_prefix : String )( p_ex : TlaEx ) : TlaEx = {
      p_ex match {
        case NameEx( name ) =>
          if ( p_boundVars.contains( name ) ) {
            val ret = NameEx( pfx( p_prefix, name ) )
            markSrc( p_ex, ret, p_srcDB )
            ret
          }
          else p_ex
        case OperEx( op : LetInOper, body ) =>
          val newdefs = op.defs.map(
            decl => decl match {
              case TlaOperDecl( name, params, declBody ) => {
                val newBody = lambda( p_boundVars ++ params.map( _.name ), p_prefix )( declBody )
                markSrc( declBody, newBody, p_srcDB )
                TlaOperDecl(
                  name,
                  params.map( renameParam( p_prefix ) ),
                  newBody
                )
              }
              case _ => decl
            }
          )
          val newBody = lambda( p_boundVars, p_prefix )( body )
          markSrc( body, newBody, p_srcDB )
          val ret =
            OperEx(
              new LetInOper( newdefs ),
              newBody
            )
          markSrc( p_ex, ret, p_srcDB )
          ret
        // assuming bounded quantification!
        case OperEx( oper, NameEx( varname ), set, body )
          if oper == TlaBoolOper.exists || oper == TlaBoolOper.forall => {
          val newName = NameEx( pfx( p_prefix, varname ) )
          markSrc( p_ex.asInstanceOf[OperEx].args.head, newName, p_srcDB )
          val newSet = lambda( p_boundVars, p_prefix )( set )
          markSrc( set, newSet, p_srcDB )
          val newBody = lambda( p_boundVars + varname, p_prefix )( body )
          markSrc( body, newBody, p_srcDB )
          val ret = OperEx( oper, newName, newSet, newBody )
          markSrc( p_ex, ret, p_srcDB )
          ret
        }
        case OperEx( oper, args@_* ) => {
          val newArgs = args.map( lambda( p_boundVars, p_prefix ) )
          args.zip( newArgs ).foreach( pa => markSrc( pa._1, pa._2, p_srcDB ) )
          val ret = OperEx( oper, newArgs : _* )
          markSrc( p_ex, ret, p_srcDB )
          ret
        }
        case _ => p_ex
      }
    }

    p_decls.map(
      decl => decl match {
        case TlaOperDecl( name, params, body ) =>
          TlaOperDecl( name, params.map( renameParam( name ) ), lambda( params.map( _.name ).toSet, name )( body ) )
        case _ => decl
      }
    )

  }

  def extract( p_decl : TlaDecl,
               p_db : BodyDB
             ) : Unit = {
    p_decl match {
      /**
        * What to do when extracting the same operator > 1 times? Currently, we skip the 2nd+.
        * Jure, 1.12.2017
        **/
      case decl : TlaOperDecl if !p_db.contains( p_decl.name ) =>
        p_db.update( decl.name, (decl.formalParams, decl.body) )
      case _ =>
    }
  }

  def extract( p_spec : TlaSpec,
               p_db : BodyDB
             ) : Unit = SpecHandler.sideeffectDecl( p_spec, extract( _, p_db ) )

  def replaceAll(p_tlaEx : TlaEx,
                 p_replacedEx : TlaEx,
                 p_newEx : TlaEx,
                 p_listener : TransformationListener
                ) : TlaEx = {
    def swap( arg : TlaEx ) : TlaEx =
      if ( arg == p_replacedEx ) {
        val ret = p_newEx.deepCopy()
        markSrc( arg, ret, p_listener )
        ret
      }
      else arg

    SpecHandler.getNewEx( p_tlaEx, swap, markSrc( _, _, p_listener ) )
  }

  def replaceWithRule(p_ex : TlaEx,
                      p_rule : TlaEx => TlaEx,
                      p_listener : TransformationListener
                     ) : TlaEx = {
    SpecHandler.getNewEx( p_ex, p_rule, markSrc( _, _, p_listener ) )
  }

  /*
  @Igor (08.01.2019). Commented out this method, as it requires precise tracking of changes, which is not always possible.

  def undoReplace( p_ex : TlaEx,
                   p_srcDB : SourceStoreImpl
                 ) : TlaEx = {
    if ( p_srcDB.contains( p_ex.ID ) ) {
      UniqueDB( p_srcDB( p_ex.ID ) )
    }
    else p_ex
  }
  */

  def unfoldOnce(p_ex : TlaEx,
                 p_bdDB : BodyDB,
                 p_listener : TransformationListener
                ) : TlaEx = {

    /**
      * Old Bug( Jure: 1.12.2017 ): inlining did not check if provided argument count matches arity,
      * because the parser would reject such TLA code. However, manual examples produced
      * demonstrated lack of exceptions thrown when the number of args provided exceeded the arity.
      *
      * This has been rectified by a checkUID in lambda.
      **/

    /**
      * Bug( Jure: 15.1.2018 ): Inlining did not look inside the operator declarations of a LET-IN
      * operator.
      */

    /**
      * Bug (Jure: 23.2.2018): Inlining adds X->X to the sourceDB
      *
      * Fixed by removing p_srcDB.update() calls with markSrc(), which performs sanity checks
      */

    def subAndID( p_operEx : TlaEx ) : TlaEx = {

      def lambda( name : String, args : TlaEx* ) : TlaEx = {
        val pbPair = p_bdDB.get( name )
        if ( pbPair.isEmpty ) return p_operEx

        var (params, body) = pbPair.get
        if ( params.size != args.size )
          throw new IllegalArgumentException(
            "Operator %s with arity %s called with %s argument%s".format( name, params.size, args.size, if ( args.size != 1 ) "s" else "" )
          )

        // Igor: Jure, please write imperative code, if you like it so. The commented code below is impossible to debug.
        for ((par, arg) <- params.zip(args)) {
          val paramName = NameEx(par.name)
          markSrc(arg, paramName, p_listener )
          body = replaceAll(body, paramName, arg, p_listener)
        }

        markSrc(p_operEx, body, p_listener )

        /*
        params.zip( args ).foreach(
          pair => body = replaceAll( body, NameEx( pair._1.name ), pair._2, p_listener )
        )
        //        Identifier.identify( body )
        markSrc( p_operEx, body, p_listener )
        */
        body
      }

      p_operEx match {
        case OperEx( op : TlaUserOper, args@_* ) => lambda( op.name, args : _* )
        case OperEx( TlaOper.apply, NameEx( name ), args@_* ) => lambda( name, args : _* )
        case _ => p_operEx
      }
    }

    val ret = SpecHandler.getNewEx( p_ex, subAndID )
    markSrc( p_ex, ret, p_listener )
    ret
  }

  def unfoldMax(p_ex : TlaEx,
                p_bdDB : BodyDB,
                p_listener : TransformationListener
               ) : TlaEx = {
    var a = p_ex
    var b = unfoldOnce( p_ex, p_bdDB, p_listener )
    while ( a != b ) {
      a = b
      b = unfoldOnce( b, p_bdDB, p_listener )
    }
    //    Identifier.identify( b )
    markSrc( p_ex, b, p_listener )
    b
  }

}
