package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{TlaEx, _}
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.standard.{
  DeclarationSorter, DeepCopy, IncrementalRenaming, ReplaceFixed,
}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier}

/**
 * TODO
 *
 * @author
 *   Jure Kukovec
 */
class Inliner(tracker: TransformationTracker, nameGenerator: UniqueNameGenerator, keepNullary: Boolean = true)
    extends TlaModuleTransformation {

  type DeclFilter = TlaOperDecl => Boolean

  private val renaming = new IncrementalRenaming(tracker)
  private val deepcopy = DeepCopy(tracker)
  private def deepCopy(ex: TlaEx): TlaEx = renaming(deepcopy.deepCopyEx(ex))

  import Inliner._

  // Bookeeping of scope, always called, but discards operators that won't be inlined
  private def extendedScope(operFilterFn: DeclFilter, operatorsInScope: Scope)(d: TlaOperDecl): Scope = d match {
    // We only inline operators if
    // - they're non-recursive, and
    // - they don't satisfy the filter function
    case decl: TlaOperDecl if !decl.isRecursive && !operFilterFn(decl) =>
      operatorsInScope + (decl.name -> decl)
    // ignore any other declaration
    case _ => operatorsInScope
  }

  // Iterative traversal of decls with a monotonically increasing scope.
  // All operator declarations are either added to the scope, or kept in the declaration list.
  // Operators are kept if they satisfy operFilterFn and added to the scope otherwise.
  private def pushDeclsIntoScope(
      operDeclFilter: DeclFilter
    )(initialScope: Scope,
      decls: Traversable[TlaDecl]): (Scope, List[TlaDecl]) =
    decls.foldLeft((initialScope, List.empty[TlaDecl])) { case ((scope, decls), decl) =>
      decl match {
        case opDecl: TlaOperDecl =>
          val newDeclBody = transform(scope)(opDecl.body)
          val newDecl = tracker.trackOperDecl { _ => opDecl.copy(body = newDeclBody) }(opDecl)
          val newScope = extendedScope(operDeclFilter, scope)(newDecl)
          if (operDeclFilter(newDecl)) (newScope, decls :+ newDecl)
          else (newScope, decls)
        case _ => (scope, decls :+ decl)
      }
    }

  // Default operator filter, we keep only nullary operators and only if keepNullary is enabled
  private def nullaryFilter(d: TlaOperDecl): Boolean = keepNullary && d.formalParams.isEmpty

  // Assume name is in scope.
  // Creates a fresh copy of the operator body and replaces formal parameter instances with the argument instances.
  def instantiateWithArgs(operatorsInScope: Scope)(name: String, args: Seq[TlaEx]): TlaEx = {
    val decl = operatorsInScope(name)

    // Note: it can happen that the body and the decl have desynced types,
    // due to the way type-checking is currently implemented for polymorphic operators.
    // We fix that below with type unification.
    val freshBody = deepCopy(decl.body)

    // Each formal parameter gets instantiated independently.
    val newBody = decl.formalParams.zip(args).foldLeft(freshBody) { case (partialBody, (fParam, arg)) =>
      ReplaceFixed(tracker)(NameEx(fParam.name)(arg.typeTag), arg)(partialBody)
    }

    // If the operator has a parametric signature, we have to substitute type parameters with concrete parameters
    // 1. Unify the operator type with the arguments.
    // 2. Apply the resulting substitution to the types in all subexpressions.
    val actualType = OperT1(args.map(_.typeTag.asTlaType1()), freshBody.typeTag.asTlaType1())
    val genericType = decl.typeTag.asTlaType1()
    val substitution = new TypeUnifier().unify(Substitution.empty, genericType, actualType) match {
      case None =>
        throw new TypingException(
            s"Inliner: Unable to unify generic signature $genericType of ${decl.name} with the concrete type $actualType",
            decl.ID)

      case Some((sub, _)) => sub
    }

    if (substitution.isEmpty) newBody
    else new TypeSubstitutor(tracker, substitution)(newBody)
  }

  // Assume name is in scope. Creates a local nullary LET-IN for call-by-name operators.
  // If Inliner is ever called 2+ times, every call but the first must have `keepNullary = true` to preserve this.
  // TODO
  def embedCallByName(nameEx: NameEx): TlaEx = nameEx

  // TODO
  def transform(operatorsInScope: Scope): TlaExTransformation = tracker.trackEx {
    // Standard application
    case OperEx(TlaOper.apply, NameEx(name), args @ _*) if operatorsInScope.contains(name) =>
      instantiateWithArgs(operatorsInScope)(name, args)

    // LET-IN extends scope
    case LetInEx(body, defs @ _*) =>
      val (newScope, remainingOpers) = pushDeclsIntoScope(nullaryFilter)(operatorsInScope, defs)
      val castDecls = remainingOpers.map(_.asInstanceOf[TlaOperDecl])
      val newBody = transform(newScope)(body)

      if (castDecls.isEmpty) newBody
      else LetInEx(newBody, castDecls: _*)(newBody.typeTag)

    // TODO
    case ex => ex
  }

  override def apply(m: TlaModule): TlaModule = {
    val declSorter = new DeclarationSorter
    // Instead of pre-building a body map, sorts operators according to
    // dependency order and iterates over a sorted collection
    val moduleWithSortedDecls = declSorter(m)

    val sortedDecls = moduleWithSortedDecls.declarations

    // Instead of building a parallel BodyMap, we build scope iteratively, as the declarations are now in order.
    val inlinedDecls = pushDeclsIntoScope(FilterFun.ALL)(emptyScope, sortedDecls)._2

    m.copy(declarations = inlinedDecls)
  }

}

object Inliner {

  type Scope = BodyMap

  def emptyScope: Scope = Map.empty

  object FilterFun {
    def ALL: TlaOperDecl => Boolean = _ => true
    def NAMED(set: Set[String]): TlaOperDecl => Boolean = d => set.contains(d.name)
  }

}
