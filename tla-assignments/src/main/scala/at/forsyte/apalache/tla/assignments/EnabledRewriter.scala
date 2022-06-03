package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.storage.SourceLocator
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.assignments.SmtFreeSymbolicTransitionExtractor
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.values.TlaBool

/**
 * Attempts to rewrite `ENABLED foo` operators into formulas that are true when action `foo` is enabled.
 *
 * @author
 *   Philip Offtermatt
 */
class EnabledRewriter(
    module: TlaModule,
    tracker: TransformationTracker,
    sourceStore: SourceStore,
    changeListener: ChangeListener)
    extends TlaExTransformation {

  /**
   * Removes the assignments x' := foo from an expression by replacing them with TRUE
   */
  private def removeAssignmentsFromExpression(ex: TlaEx): TlaEx = {
    val res = ex match {
      case OperEx(oper, args @ _*) =>
        oper match {
          case ApalacheOper.assign =>
            ValEx(TlaBool(true))(Typed(BoolT1))
          case _ =>
            OperEx(oper, args.map(removeAssignmentsFromExpression): _*)(ex.typeTag)
        }
      case _ =>
        ex
    }
    res
  }

  /**
   * TODO: Extracts a map of assignments primeVar := foo from an expression
   */
  private def extractAssignmentsFromExpression(ex: TlaEx): Map[String, TlaEx] = {
    Map.empty
  }

  /**
   * TODO: Rewrite occurrences of primed variable as unprimed expression; needs to be done iteratively to replace more and more variables
   */

  private def transformEnabled(ex: TlaEx): TlaEx = {
    val vars = module.varDeclarations.map(_.name)

    val sourceLoc = SourceLocator(sourceStore.makeSourceMap, changeListener)

    val operMap = BodyMapFactory.makeFromDecls(module.operDeclarations)

    val transitionPairs = SmtFreeSymbolicTransitionExtractor(tracker, sourceLoc)(vars.toSet, ex, operMap)

    val transitionsWithoutAssignments = transitionPairs.map(symbTrans => {
      val assignmentEx = symbTrans._2
      val modifiedEx = removeAssignmentsFromExpression(assignmentEx)
      print("\n::::::::::::::::\n")
      print(modifiedEx.toString())
      print("\n::::::::::::::::\n")
    })
    print("\n--------------------------------\n")
    print(ex.toString())
    print("\n================================\n")
    print(transitionsWithoutAssignments.toString())
    print("\n--------------------------------\n")
    NullEx
  }

  override def apply(ex: TlaEx): TlaEx = {
    ex match {
      case OperEx(TlaActionOper.enabled, arg) =>
        transformEnabled(arg)
      case OperEx(oper, args @ _*) =>
        new OperEx(oper, args.map(arg => this(arg)): _*)(ex.typeTag)
      case LetInEx(_, _) =>
        throw new NotInKeraError("There should be no let-in expressions left after inlining", ex)
      case _ => ex
    }
  }
}
