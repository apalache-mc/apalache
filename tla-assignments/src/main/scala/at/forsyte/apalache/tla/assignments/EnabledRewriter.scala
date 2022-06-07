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
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

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
    ex match {
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
  }

  /**
   * Extracts a map of assignments primeVar := foo from an expression
   */
  private def extractAssignmentsFromExpression(ex: TlaEx): Map[String, TlaEx] = {
    ex match {
      case OperEx(oper, args @ _*) =>
        oper match {
          case ApalacheOper.assign =>
            // by the meaning of the assign operator, will be the name of a (primed) variables
            // there should not be none, so we'll throw an exception if it is the case
            val varName = findPrimedVariableInExpression(args(0))
            if (varName.isEmpty) {
              throw new LirError("Unexpected: did not find a primed variable on the left-hand side" +
                "of the assign statement: " + ex.toString())
            }
            return Map[String, TlaEx](
                (
                    varName.get,
                    args(1),
                )
            )
          case _ =>
            return args
              .map(extractAssignmentsFromExpression)
              .foldLeft(
                  Map.empty[String, TlaEx]
              ) { case (acc, newMap) =>
                acc.++(newMap)
              }
        }
      case _ =>
        Map.empty[String, TlaEx]
    }
  }

  /*
   * Finds some occurence of a primed variable in the expression and returns its name.
   * Throws an exception if there are multiple primed variables in the expression.
   */
  private def findPrimedVariableInExpression(ex: TlaEx): Option[String] = {
    ex match {
      case NameEx(_) => None
      case LetInEx(_, _) =>
        throw new NotInKeraError("There should be no let-in expressions left after inlining", ex)
      case OperEx(TlaActionOper.prime, NameEx(name)) => Some(name)
      case OperEx(_, args @ _*) =>
        args.map(findPrimedVariableInExpression).foldLeft(None: Option[String]) { case (curOption, newOption) =>
          (curOption, newOption) match {
            case (None, None)      => None
            case (Some(str), None) => Some(str)
            case (None, Some(str)) => Some(str)
            case (Some(str), Some(otherstr)) =>
              throw new LirError("Expect to find only one primed variable" +
                s"in the expression, but found these two variables primed: ${str}, ${otherstr}")
          }
        }
      case _ => None
    }
  }

  /**
   * Flattens the map of assignments, e.g.
   *
   * {{{Map(x' -> y' + 1, y' -> x + 5)}}} should become {{{Map(x' -> (x + 5) + 1, y' -> x + 5)}}}
   *
   * There should be no circular dependencies, e.g. {{{Map(x' -> y' + 1, y' -> x + 5)}}}. Then, the output is guaranteed
   * to have no primed variables on right-hand-sides.
   */
  private def flattenAssignments(assignmentMap: Map[String, TlaEx]): Map[String, TlaEx] = {
    def flattenOnce(assignmentMap: Map[String, TlaEx]): Map[String, TlaEx] = {
      assignmentMap.map { case (name, assignment) =>
        (name, flattenEx(assignment, assignmentMap))
      }
    }

    var currentMap = assignmentMap

    // at most, need to flatten once for every variable (unless there are circular dependencies)
    for (_ <- 1 to assignmentMap.size) {
      val newMap = flattenOnce(assignmentMap)
      // no variables are replaced, so can abort early
      if (currentMap == newMap) {
        return currentMap
      }
      currentMap = newMap
    }
    currentMap
  }

  /*
   * In the provided expression, replace all occurrences of names
   * that are keys in the assignment map by their respective assigned expression,
   * i.e. the result of {{{assignmentMap.getOrElse(name, ex)}}}
   */
  private def flattenEx(ex: TlaEx, assignmentMap: Map[String, TlaEx]): TlaEx = {
    ex match {
      case OperEx(TlaActionOper.prime, NameEx(name)) =>
        // replace a name expression by its assignment
        // or leave it if no assignment exists for the name expression
        assignmentMap.getOrElse(name, ex)
      case OperEx(oper, args @ _*) =>
        OperEx(oper, args.map(arg => flattenEx(arg, assignmentMap)): _*)(ex.typeTag)
      case LetInEx(_, _) =>
        throw new NotInKeraError("There should be no let-in expressions left after inlining", ex)
      case _ => ex
    }
  }

  private def transformEnabled(ex: TlaEx): TlaEx = {
    val vars = module.varDeclarations.map(_.name)

    val sourceLoc = SourceLocator(sourceStore.makeSourceMap, changeListener)

    val operMap = BodyMapFactory.makeFromDecls(module.operDeclarations)

    val transitionPairs = SmtFreeSymbolicTransitionExtractor(tracker, sourceLoc)(vars.toSet, ex, operMap)

    val transitionsWithoutAssignments = transitionPairs.map(symbTrans => {
      val assignmentEx = symbTrans._2
      val assignments = flattenAssignments(extractAssignmentsFromExpression(assignmentEx))
      val modifiedEx = flattenEx(removeAssignmentsFromExpression(assignmentEx), assignments)
      modifiedEx
    })

    OperEx(TlaBoolOper.or, transitionsWithoutAssignments: _*)(Typed(BoolT1))
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
