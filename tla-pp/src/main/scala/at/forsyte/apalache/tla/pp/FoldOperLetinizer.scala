package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
 * Replaces FoldSet( A, ..., ...), where A(p,q) == X with FoldSet( LET localA(p,q) == X IN localA, ..., ...)
 *
 * The purpose of this is to embed the operator definition at the call-by-name site, to allow for
 * a) the deletion of A from the operator declaration set
 * b) the removal of a BodyMap dependency in FoldSet rewriting.
 *
 * <p>Example: `A(p,q) == p + q`, `FoldSet(A, 0, {1,2,3})` becomes
 * `FoldSet( LET localA(p,q) == p + q IN localA, 0, {1,2,3})`.
 * </p>
 *
 * @author Jure Kukovec
 */
class FoldOperLetinizer(tracker: TransformationTracker, operMap: BodyMap, nameGenerator: UniqueNameGenerator)
    extends TlaExTransformation {
  override def apply(ex: TlaEx): TlaEx = transform(ex)

  private def transform: TlaExTransformation = tracker.trackEx {
    case foldSetEx @ OperEx(ApalacheOper.foldSet, nameEx: NameEx, base, set) =>
      OperEx(ApalacheOper.foldSet, replaceFromName(nameEx), base, set)(foldSetEx.typeTag)
    case foldSeqEx @ OperEx(ApalacheOper.foldSeq, nameEx: NameEx, base, seq) =>
      OperEx(ApalacheOper.foldSeq, replaceFromName(nameEx), base, seq)(foldSeqEx.typeTag)

    // recursive processing of composite operators
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map apply
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex @ LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = transform(d.body)) }
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)(ex.typeTag)
    case ex => ex
  }

  // Swap out one call-by-name for a LET-IN
  private def replaceFromName(nameEx: NameEx): TlaEx =
    operMap.get(nameEx.name) match {
      case Some(d: TlaOperDecl) =>
        val newName = nameGenerator.newName()
        val declCopy = d.copy(name = newName) // same parameter names, same body
        LetInEx(NameEx(newName)(nameEx.typeTag), declCopy)(nameEx.typeTag)
      case None =>
        throw new TlaInputError(s"Cannot fold with operator ${nameEx.name}: no definition found.", Some(nameEx.ID))
    }
}

object FoldOperLetinizer {
  def apply(tracker: TransformationTracker, operMap: BodyMap, nameGenerator: UniqueNameGenerator): FoldOperLetinizer = {
    new FoldOperLetinizer(tracker, operMap, nameGenerator)
  }
}
