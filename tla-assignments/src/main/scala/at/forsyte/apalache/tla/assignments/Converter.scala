package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._

/**
  * Object responsible for pre-processing input before it is passed to the
  * [[at.forsyte.apalache.tla.assignments.assignmentSolver solver]].
  */
object Converter {
  protected val NEXT_STEP_DEFAULT_NAME = "Next"
  protected val INIT_STEP_DEFAULT_NAME = "Init"
  protected val m_bodyDB               = new BodyDB()
  protected val m_srcDB                = new SourceDB()


  def extract( p_decls : TlaDecl*
             )
             ( implicit db : BodyDB = m_bodyDB
             ) : Unit = {

    p_decls.foreach( OperatorHandler.extract( _, db ) )
  }

  def getVars( p_decls : TlaDecl* ) : Set[String] = {
    p_decls.withFilter( _.isInstanceOf[TlaVarDecl] ).map( _.name ).toSet
  }

  def inlineAll(
                 p_expr : TlaEx
               )
               (
                 implicit bodyDB : BodyDB = m_bodyDB,
                 srcDB : SourceDB = m_srcDB
               ) : TlaEx = {

    OperatorHandler.unfoldMax( p_expr, bodyDB, srcDB )
  }

  def sanitizeByName(
                      p_operName : String
                    )
                    (
                      implicit bodyDB : BodyDB = m_bodyDB,
                      srcDB : SourceDB = m_srcDB
                    ) : TlaEx = {

    bodyDB.body( p_operName ).map( sanitize( _ )( bodyDB, srcDB ) ).getOrElse( NullEx )
  }

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

    OperatorHandler.replaceWithRule( inlineAll( p_expr )( bodyDB, srcDB ), rewriteEQ, m_srcDB )
  }

  def apply( p_expr : TlaEx, p_decls : TlaDecl* ) : Option[TlaEx] = {
    extract( p_decls : _* )
    val san = sanitize( p_expr )
    if ( san.isNull ) None
    else Some( san )
  }

  def apply( p_opName : String, p_decls : TlaDecl* ) : Option[TlaEx] = {
    extract( p_decls : _* )
    val san = sanitizeByName( p_opName )
    if ( san.isNull ) None
    else Some( san )
  }

}
