package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.plugins.{Identifier, OperatorDB, OperatorSubstitution, Substitutor}

import scala.io.Source
import java.io.File

/**
  * Object responsible for pre-processing input before it is passed to the
  * [[at.forsyte.apalache.tla.assignments.assignmentSolver solver]].
  */
object sanitizer {
  protected val NEXT_STEP_DEFAULT_NAME = "Next"
  protected val m_bodyDB               = new BodyDB()
  protected val m_srcDB                = new SourceDB()


  def extract( path:String, nextStepName: String = NEXT_STEP_DEFAULT_NAME ) : Option[OperEx] = {
    val importer = new SanyImporter()

    val (rootName, modules) = importer.loadFromFile( new File(path) )
    val formulaCandidate =
      modules(rootName).declarations.find { _.name == nextStepName} match {
        case Some(d: TlaOperDecl) =>
          d.body match {
            case OperEx( _, _@_* ) => d.body.asInstanceOf[OperEx]
            case _ => NullEx
          }

        case _ =>
          NullEx
      }

    val vars = (
      for {decl <- modules(rootName).declarations if decl.isInstanceOf[TlaVarDecl]}
        yield NameEx(decl.name)
      ).toSet

    for {decl <- modules(rootName).declarations if decl.isInstanceOf[TlaOperDecl]}
      OperatorHandler.extractOper( decl, m_bodyDB )
//      OperatorSubstitution.extractOper(decl.asInstanceOf[TlaOperDecl])


    if( formulaCandidate == NullEx ) return None

    Some(formulaCandidate.asInstanceOf[OperEx])

  }

  def sanitize( expr: TlaEx ): (TlaEx,TlaEx) = {
    /**
      * Tasks:
      *   - Inline operators  - check
      *   - change "a = b" to "a \in B" - check
      *   - ???
      *   - profit
      */


//    val inlined = SpecHandler.getNewEx( expr, Substitutor.applyReplace )
    val inlined = OperatorHandler.unfoldMax( expr, m_bodyDB, m_srcDB  )

    def rewriteEQ(tlaEx : TlaEx) : TlaEx = {
      tlaEx match {
        case OperEx( TlaOper.eq, lhs, rhs ) => {
          OperEx(TlaSetOper.in, lhs, OperEx( TlaSetOper.enumSet, rhs ) )
//          Identifier.identify( ret )
//          m_srcDB.put( ret.ID, tlaEx.ID )
//          ret
        }
        case _ => tlaEx
      }
    }

    val rewritten = OperatorHandler.replaceWithRule( inlined, rewriteEQ, m_srcDB )

//    val rewritten = SpecHandler.getNewEx( inlined, rewriteEQ )

    // ???

//    Identifier.identify(rewritten)

    return (expr, rewritten) // profit

  }

  def apply(path:String, nextStepName: String = NEXT_STEP_DEFAULT_NAME ) : Option[(TlaEx,TlaEx)] = {
    extract(path,nextStepName).map(sanitize)
  }
}
