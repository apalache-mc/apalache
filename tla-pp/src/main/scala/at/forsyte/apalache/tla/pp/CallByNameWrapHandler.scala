package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
 * Wraps instances of call-by-name with the ApalacheOper.callByName operator, to allow passes to ignore certain
 * forms of processing for these expressions (e.g. not removing the local LET-IN definition)
 * or unwraps them when the operator is no longer necessary to guard against preprocessing.
 */
class CallByNameWrapHandler(tracker: TransformationTracker) {
//  We create class wrappers, so `tr.getClass.getSimpleName` works in the passes
  sealed class Wrap(tr: TlaExTransformation) extends TlaExTransformation {
    override def apply(arg: TlaEx): TlaEx = tr(arg)
  }
  sealed class Unwrap(tr: TlaExTransformation) extends TlaExTransformation {
    override def apply(arg: TlaEx): TlaEx = tr(arg)
  }

  private def wrapEx(nameEx: NameEx) = OperEx(ApalacheOper.callByName, nameEx)(nameEx.typeTag)

  def wrap: Wrap = new Wrap(tracker.trackEx {
    // Currently, we only support call-by-name in folding
    case foldEx @ OperEx(op @ (ApalacheOper.foldSet | ApalacheOper.foldSeq), nameEx: NameEx, base, set) =>
      OperEx(op, wrapEx(nameEx), wrap(base), wrap(set))(foldEx.typeTag)

    // recursive processing of composite operators
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map wrap
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex @ LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = wrap(d.body)) }
      val newBody = wrap(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)(ex.typeTag)
    case ex => ex
  })

  def unwrap: Unwrap = new Unwrap(tracker.trackEx {
    // Currently, we only support call-by-name in folding
    case foldEx @ OperEx(op @ (ApalacheOper.foldSet | ApalacheOper.foldSeq), OperEx(ApalacheOper.callByName, letInEx),
            base, set) =>
      OperEx(op, unwrap(letInEx), unwrap(base), unwrap(set))(foldEx.typeTag)

    // recursive processing of composite operators
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map unwrap
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex @ LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = unwrap(d.body)) }
      val newBody = unwrap(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)(ex.typeTag)
    case ex => ex
  })
}

object CallByNameWrapHandler {
  def apply(tracker: TransformationTracker): CallByNameWrapHandler = {
    new CallByNameWrapHandler(tracker)
  }
}
