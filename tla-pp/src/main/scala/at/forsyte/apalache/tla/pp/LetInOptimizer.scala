package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.transformations._
import at.forsyte.apalache.tla.lir._

/**
 * <p>LetInOptimizer looks for unused let-in definitions and removes them. Such unused definitions can be introduced
 * by preprocessing passes such as Skolemization.</p>
 *
 * <p>This transformation assumes that all names are unique, that is, it should be used after `IncrementalRenaming`.
 *
 * @author Igor Konnov
 */
class LetInOptimizer(tracker: TransformationTracker) extends TlaExTouchTransformation {
  // this set stores the names that are not known to be used yet
  private var unusedNames: Set[String] = Set.empty

  override def apply(input: KeepOrTouchEx): KeepOrTouchEx = {
    transform(input)
  }

  private def transform: TlaExTouchTransformation = tracker.trackTouchEx(_.flatMap {
    case ex @ ValEx(_) =>
      keep(ex)

    case ex @ NameEx(name) =>
      // if this name is on the list of unused names, remove it from the list
      unusedNames -= name
      keep(ex)

    case ex @ OperEx(oper, args @ _*) =>
      val targs = args.map(a => transform(touch(a)))
      if (targs.forall(_.isLeft)) {
        // No argument has changed.
        keep(ex)
      } else {
        // At least one argument has changed: Produce a new expression and tag it as to be touched.
        touch(OperEx(oper, targs.map(a => a.fold(e1 => e1, e2 => e2)): _*)(ex.typeTag))
      }

    case letInEx @ LetInEx(body, decls @ _*) =>
      def transformDecl(decl: TlaOperDecl): (TlaOperDecl, Boolean) = {
        transform(touch(decl.body))
          .map { newBody =>
            // copy the declaration if the body has changed (don't forget to track the change)
            (tracker.trackOperDecl(_.copy(body = newBody))(decl), true)
          } // or return the old declaration
          .getOrElse((decl, false))
      }

      // all names are yet to be tagged as used (or unused)
      val defNames = decls.map(_.name)
      unusedNames ++= defNames
      // Transform the declarations. Note that they may add/remove names to/from unusedNames.
      // If a declaration A uses a declaration B,
      // and neither A nor B are used in the body, we may have a false positive.
      // A more precise analysis would require computation of def-use chains.
      val trBody = transform(touch(body))
      val trDecls = decls.map(transformDecl).filter(p => !unusedNames.contains(p._1.name))
      if (trDecls.forall(!_._2) && trBody.isLeft && trDecls.length == decls.length) {
        keep(letInEx)
      } else {
        // A change in: bodies of the operator declarations, in the expression under the let-in,
        // or in the number of declarations. Construct a new let-in expression
        val newBody = trBody.fold(e1 => e1, e2 => e2)
        if (trDecls.isEmpty) {
          touch(newBody)
        } else {
          touch(LetInEx(newBody, trDecls.map(_._1): _*)(letInEx.typeTag))
        }
      }

    case ex @ _ =>
      keep(ex)
  })
}
