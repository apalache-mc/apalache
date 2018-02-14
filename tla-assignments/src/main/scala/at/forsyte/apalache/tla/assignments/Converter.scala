package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.control.{LetInOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.plugins.Identifier
import com.google.inject.Singleton

/**
  * Object responsible for pre-processing input before it is passed to the
  * [[at.forsyte.apalache.tla.assignments.assignmentSolver solver]].
  */
@Singleton
class Converter {
  // Igor: this class does a lot of things. Write comments on what the outcome is.
  // Igor: Does this class have to be stateful?
  //
  // Igor: Let's find a better name for this class.
  //
  // Igor @ 27/12/2017: converted from a singleton to a class.
  // Let Guice take care of instantiating the object rightly.
  protected val NEXT_STEP_DEFAULT_NAME = "Next"
  protected val INIT_STEP_DEFAULT_NAME = "Init"
  protected val m_bodyDB               = new BodyDB()
  protected val m_srcDB                = new SourceDB()

  // The methods that are not part of the interface should be declared private.
  def extract( p_decls : TlaDecl*
             )
             ( implicit db : BodyDB = m_bodyDB
             ) : Unit = {

    p_decls.foreach( OperatorHandler.extract( _, db ) )
  }

  def getVars( p_decls : TlaDecl* ) : Set[String] = {
    p_decls.withFilter( _.isInstanceOf[TlaVarDecl] ).map( _.name ).toSet
  }

  // The methods that are not part of the interface should be declared private.
  def inlineAll(
                 p_expr : TlaEx
               )
               (
                 implicit bodyDB : BodyDB = m_bodyDB,
                 srcDB : SourceDB = m_srcDB
               ) : TlaEx = {

    OperatorHandler.unfoldMax( p_expr, bodyDB, srcDB )
  }

  // The methods that are not part of the interface should be declared private.
  def unchangedExplicit(
                         p_ex : TlaEx
                       )(
                         implicit srcDB : SourceDB = m_srcDB
                       ) : TlaEx = {

    def exFun( ex : TlaEx ) : TlaEx = {
      def lambda( x : TlaEx ) =
        Builder.in( Builder.prime( x ), Builder.enumSet( x ) )

      val ret = ex match {
        case OperEx( TlaActionOper.unchanged, arg ) =>
          arg match {
            case OperEx( TlaFunOper.tuple, args@_* ) =>
              Builder.and( args.map( lambda ) : _* )
            case NameEx( _ ) => lambda( arg )
            case _ => ex
          }
        case _ => ex
      }

      Identifier.identify(ret)
      ret
    }

    OperatorHandler.replaceWithRule( p_ex, exFun, srcDB )
  }

  def iteToCase(
                 p_ex : TlaEx
               )(
                 implicit srcDB : SourceDB = m_srcDB
               ) : TlaEx = {
    def exFun( ex: TlaEx ) : TlaEx = {
      ex match {
        case OperEx( TlaControlOper.ifThenElse, condEx, thenEx, elseEx ) =>
          OperEx( TlaControlOper.caseWithOther, elseEx, condEx, thenEx )
        case _ => ex
      }
    }

    OperatorHandler.replaceWithRule( p_ex, exFun, srcDB )
  }

  def explicitLetIn(
                     p_ex : TlaEx
                   )(
                     implicit srcDB : SourceDB = m_srcDB
                   ) : TlaEx = {
    def exFun( ex : TlaEx ) : TlaEx = {
      ex match {
        case OperEx( oper: LetInOper, body ) => {

          val bodyDB = new BodyDB()
          oper.defs.foreach( OperatorHandler.extract( _, bodyDB ) )

          inlineAll( body )( bodyDB, srcDB )
        }
        case _ => ex
      }
    }

    OperatorHandler.replaceWithRule( p_ex, exFun, srcDB )
  }

  // The methods that are not part of the interface should be declared private.
  def sanitizeByName(
                      p_operName : String
                    )
                    (
                      implicit bodyDB : BodyDB = m_bodyDB,
                      srcDB : SourceDB = m_srcDB
                    ) : TlaEx = {

    bodyDB.body( p_operName ).map( sanitize( _ )( bodyDB, srcDB ) ).getOrElse( NullEx )
  }

  // The methods that are not part of the interface should be declared private.
  def sanitize(
                p_expr : TlaEx
              )
              (
                implicit bodyDB : BodyDB = m_bodyDB,
                srcDB : SourceDB = m_srcDB
              ) : TlaEx = {
    def rewriteEQ( tlaEx : TlaEx ) : TlaEx = {
      tlaEx match {
        case OperEx( TlaOper.eq, lhs, rhs ) => {
          OperEx( TlaSetOper.in, lhs, OperEx( TlaSetOper.enumSet, rhs ) )
        }
        case _ => tlaEx
      }
    }

    val inlined = inlineAll( p_expr )( bodyDB, srcDB )

    val eqReplaced = OperatorHandler.replaceWithRule( inlined, rewriteEQ, srcDB )

    /* val ucReplaced = */ unchangedExplicit( eqReplaced )( srcDB )

//    iteToCase( ucReplaced )( srcDB )


  }

  // Igor: normally, the most important methods come first in a class declaration.
  // Igor: why is this method declared with apply? What is special about it?
  def apply( p_expr : TlaEx, p_decls : TlaDecl* ) : Option[TlaEx] = {
    Identifier.identify( p_expr )
    p_decls.foreach( Identifier.identify )
    extract( p_decls : _* )
    val san = sanitize( p_expr )
    if ( san.isNull ) None
    else {
      Identifier.identify( san )
      Some( san )
    }
  }

  // Igor: normally, the most important methods come first in a class declaration.
  // Igor: why is this method declared with apply? What is special about it?
  def apply( p_opName : String, p_decls : TlaDecl* ) : Option[TlaEx] = {
    p_decls.foreach( Identifier.identify )
    extract( p_decls : _* )
    val san = sanitizeByName( p_opName )
    if ( san.isNull ) None
    else Some( san )
  }

}
