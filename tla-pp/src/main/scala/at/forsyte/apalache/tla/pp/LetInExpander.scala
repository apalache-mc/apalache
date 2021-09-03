package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaOper}
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

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
  override def apply(ex: TlaEx): TlaEx = transform(ex)

  def transform: TlaExTransformation = tracker.trackEx {
    // interesting case
    case letInEx @ LetInEx(body, defs @ _*) =>
      /** LET-IN may be nested in the body ... */
      val expandedBody = transform(body)

      /** .. or another operator */
      val expandedDefs = defs map tracker.trackOperDecl { d => d.copy(body = transform(d.body)) }

      def needsExpansion(d: TlaOperDecl): Boolean = {
        // Expand only the definitions that:
        //  1. Either have at least one parameter (if keepNullary = false), or
        //     have any number of parameters (if keepNullary = true)
        //  2. Are not defining a LAMBDA operator, which is treated by the special case below.
        (!keepNullary || d.formalParams.nonEmpty) && d.name != "LAMBDA"
      }

      val (defsToExpand, defsToKeep) = expandedDefs.partition(needsExpansion)

      /** create a map of definitions from the ones that have to be expanded */
      val bodyMap = BodyMapFactory.makeFromDecls(defsToExpand)

      val expandedLetIn =
        if (defsToKeep.nonEmpty) {
          LetInEx(expandedBody, defsToKeep: _*)(letInEx.typeTag) // nullary definitions are still there
        } else {
          expandedBody // all definitions were expanded
        }

      // Inline the operators using the map of definitions
      InlinerOfUserOper(bodyMap, tracker)(expandedLetIn)

    // Ignore the call-by-name site tagged with ApalacheOper.callByName, since it
    // has a local LET-IN definition that should persist
    case ex @ OperEx(ApalacheOper.callByName, LetInEx(body, decl)) =>
      // but clean up inside the decl, potentially
      val newDecl = tracker.trackOperDecl { d => d.copy(body = transform(d.body)) }(decl)
      if (decl == newDecl) ex
      else OperEx(ApalacheOper.callByName, LetInEx(body, newDecl)(ex.typeTag))(ex.typeTag)

    // this is the special form for LAMBDAs
    case OperEx(TlaOper.apply, LetInEx(NameEx("LAMBDA"), TlaOperDecl("LAMBDA", params, lambdaBody)), args @ _*) =>
      // Substitute params with args in the body of the lambda expression.
      // I don't think we need to deep copy lambdaBody, as it should appear only once.
      assert(params.length == args.length)
      params.zip(args).foldLeft(lambdaBody) {
        // replace every parameter with the respective argument
        case (expr, (param, arg)) =>
          ReplaceFixed(tracker)(NameEx(param.name)(arg.typeTag), arg)(expr)
      }

    // recursive processing of composite operators
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map transform
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex => ex
  }
}

object LetInExpander {
  def apply(tracker: TransformationTracker, keepNullary: Boolean)(implicit typeTag: TypeTag): LetInExpander = {
    new LetInExpander(tracker, keepNullary)
  }
}
