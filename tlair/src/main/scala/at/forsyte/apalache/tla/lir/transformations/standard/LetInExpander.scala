package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory

/**
  * <p>A transformation which replaces all occurrences of LET-IN expressions with
  * copies of their bodies, in which LET-IN defined operators have been expanded.
  * If the `keepNullary` flag is set to true, only operators with strictly positive arity get expanded.</p>
  *
  * <p>Example: `LET X(a) == a + b IN X(0) > 1` becomes `1 + b > 1`. </p>
  *
  * @author Jure Kukovec
  */
class LetInExpander(tracker: TransformationTracker, keepNullary: Boolean) extends TlaExTransformation {
  override def apply(ex: TlaEx) = transform(ex)

  def transform: TlaExTransformation = tracker.track {
    // interesting case
    case LetInEx(body, defs @ _*) =>
      /** LET-IN may be nested in the body ... */
      val expandedBody = transform(body)

      /** .. or another operator */
      val expandedDefs = defs map { d =>
        d.copy(body = transform(d.body))
      }

      def needsExpansion(d: TlaOperDecl): Boolean = !keepNullary || d.formalParams.nonEmpty

      val (defsToExpand, defsToKeep) = expandedDefs.partition(needsExpansion)

      /** create a map of definitions from the ones that have to be expanded */
      val bodyMap = BodyMapFactory.makeFromDecls(defsToExpand)

      val expandedLetIn =
        if (defsToKeep.nonEmpty) {
          LetInEx(expandedBody, defsToKeep: _*) // nullary definitions are still there
        } else {
          expandedBody                          // all definitions were expanded
        }

      /** Inline the operators using the map of definitions */
      InlinerOfUserOper(bodyMap, tracker)(expandedLetIn)

      // recursive processing of composite operators
    case ex@OperEx(op, args@_*) =>
      val newArgs = args map transform
      if (args == newArgs) ex else OperEx(op, newArgs: _*)

    case ex => ex
  }
}

object LetInExpander {
  def apply(tracker: TransformationTracker, keepNullary: Boolean): LetInExpander = {
    new LetInExpander(tracker, keepNullary)
  }
}