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
  val NEXT_STEP_DEFAULT_NAME = "Next"

  // filename without .tla!!


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
      OperatorSubstitution.extractOper(decl.asInstanceOf[TlaOperDecl])


    if( formulaCandidate == NullEx ) return None

    return Some(formulaCandidate.asInstanceOf[OperEx])

  }

  def sanitize( expr: TlaEx ): (TlaEx,TlaEx) = {
    /**
      * Tasks:
      *   - Inline operators
      *   - change "a = b" to "a \in B"
      *   - ???
      *   - profit
      */


    val inlined = SpecHandler.getNewEx( expr, Substitutor.applyReplace )

    def rewriteEQ(tlaEx : TlaEx) : TlaEx = {
      tlaEx match {
        case OperEx( TlaOper.eq, lhs, rhs ) => OperEx(TlaSetOper.in, lhs, OperEx( TlaSetOper.enumSet, rhs ) )
        case _ => tlaEx
      }
    }

    val rewritten = SpecHandler.getNewEx( inlined, x => x )//rewriteEQ )

    // ???

    Identifier.identify(rewritten)

    return (expr, rewritten) // profit

  }

  def apply(path:String, nextStepName: String = NEXT_STEP_DEFAULT_NAME ) : Option[(TlaEx,TlaEx)] = {
    extract(path,nextStepName).map(sanitize)
  }
}
