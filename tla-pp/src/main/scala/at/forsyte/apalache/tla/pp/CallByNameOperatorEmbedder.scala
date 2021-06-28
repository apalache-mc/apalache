package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory}
import at.forsyte.apalache.tla.lir.transformations.standard.DeepCopy
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
 * Replaces instances of call-by-name, identified by the ApalacheOper.callByName wrapper, with
 * a LET-expression, embedding the operator definition.
 *
 * The purpose of this is to allow for
 * a) the deletion of A from the operator declaration set
 * b) the removal of a BodyMap dependency in FoldX rewriting.
 * *
 * Example: `A(p,q) == p + q`, `CallByName(A) ` becomes
 * `CallByName(LET localA(p,q) == p + q IN localA)`
 *
 * @author Jure Kukovec
 */
class CallByNameOperatorEmbedder(tracker: TransformationTracker, operMap: BodyMap, nameGenerator: UniqueNameGenerator)
    extends TlaExTransformation {
  override def apply(ex: TlaEx): TlaEx = transform(operMap)(ex)

  private val deepCopy: TlaExTransformation = DeepCopy(tracker).deepCopyEx

  private def transform(bodyMap: BodyMap): TlaExTransformation = tracker.trackEx {
    case OperEx(ApalacheOper.callByName, nameEx: NameEx) =>
      OperEx(ApalacheOper.callByName, replaceFromName(bodyMap, nameEx))(nameEx.typeTag)

    // recursive processing of composite operators
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map transform(bodyMap)
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex @ LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = transform(bodyMap)(d.body)) }
      val newMap = BodyMapFactory.makeFromDecls(newDefs, bodyMap)
      val newBody = transform(newMap)(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)(ex.typeTag)
    case ex => ex
  }

  // Swap out one call-by-name for a LET-IN
  private def replaceFromName(bodyMap: BodyMap, nameEx: NameEx): TlaEx =
    bodyMap.get(nameEx.name) match {
      case Some(d @ TlaOperDecl(_, params, body)) =>
        val newName = nameGenerator.newName()
        // same parameter names, same body (copy)
        val declCopy = TlaOperDecl(newName, params, deepCopy(body))(d.typeTag)
        LetInEx(NameEx(newName)(nameEx.typeTag), declCopy)(nameEx.typeTag)
      case None =>
        throw new TlaInputError(s"Cannot fold with operator ${nameEx.name}: no definition found.", Some(nameEx.ID))
    }
}

object CallByNameOperatorEmbedder {
  def apply(tracker: TransformationTracker, operMap: BodyMap,
      nameGenerator: UniqueNameGenerator): CallByNameOperatorEmbedder = {
    new CallByNameOperatorEmbedder(tracker, operMap, nameGenerator)
  }
}
