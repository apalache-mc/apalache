package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{TlaEx, _}
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.standard.{
  DeclarationSorter, DeepCopy, IncrementalRenaming, ReplaceFixed,
}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}
import at.forsyte.apalache.tla.pp.Inliner.FilterFun
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier}

/**
 * Given a module m, with global operators F1,...,Fn _in dependency order_, Inliner performs the following
 * transformation:
 *   - For each i, replaces all application instances Fi(a1i, ..., aki) in m, where Fi(p1i,...,pki) == ei, with
 *     ei[a1/p1i, ..., aki/pki]
 *   - Replaces each instance of LET G1(q11,...,qk1) == g1 ... Gm(q1m, ..., qkm) == gm IN f, with:
 *     - f, inlined by the previous rule, as if G1, ..., Gm were global, if `keepNullary` is `false`, or,
 *     - LET Gj1 == gj1 ... Gjl == gjl
 *   - For each instance of call-by-name A (where a definition A(p1,...,pk) == e exists in scope), replaces
 *     - A with LET A_LOCAL(p1,...,pk) = e IN A_LOCAL
 *
 * @author
 *   Jure Kukovec
 */
class Inliner(
    tracker: TransformationTracker,
    nameGenerator: UniqueNameGenerator,
    keepNullary: Boolean = true,
    toplevelFilter: Inliner.DeclFilter = FilterFun.ALL)
    extends TlaModuleTransformation {

  private val renaming = new IncrementalRenaming(tracker)
  private val deepcopy = DeepCopy(tracker)
  private def deepCopy(ex: TlaEx): TlaEx = renaming(deepcopy.deepCopyEx(ex))

  import Inliner._

  // Bookeeping of scope, always called, but discards operators that won't be inlined
  private def extendedScope(scope: Scope, scopeFilter: DeclFilter)(d: TlaOperDecl): Scope = d match {
    // We only inline operators (i.e. track them in scope) if
    // - they're non-recursive, and
    // - they satisfy the scope filter function
    case decl: TlaOperDecl if !decl.isRecursive && scopeFilter(d) =>
      scope + (decl.name -> decl)
    // ignore any other declaration
    case _ => scope
  }

  // Iterative traversal of decls with a monotonically increasing scope.
  // Some operator declarations are added to the scope, some are kept in the declaration list.
  // Operators are added to the scope if they satisfy scopeFilter and kept if they satisfy
  // operDeclFilter. By default, operDeclFilter = !nonNullaryFilter, scopeFilter = nonNullaryFilter
  private def pushDeclsIntoScope(
      operDeclFilter: DeclFilter = negateFilter(nonNullaryFilter),
      scopeFilter: DeclFilter = nonNullaryFilter,
    )(initialScope: Scope,
      decls: Traversable[TlaDecl]): (Scope, List[TlaDecl]) =
    decls.foldLeft((initialScope, List.empty[TlaDecl])) { case ((scope, decls), decl) =>
      decl match {
        case opDecl: TlaOperDecl =>
          // First, process the operator body in the current scope
          val newDeclBody = transform(scope)(opDecl.body)
          // Source tracking
          val newDecl = tracker.trackOperDecl { _ => opDecl.copy(body = newDeclBody) }(opDecl)
          // then, possibly extend scope with the new declaration
          val newScope = extendedScope(scope, scopeFilter)(newDecl)
          // Finally, store the declaration in the list if necessary
          if (operDeclFilter(newDecl)) (newScope, decls :+ newDecl)
          else (newScope, decls)
        case _ => (scope, decls :+ decl)
      }
    }

  // Default scope filter, we add nullary operators only if keepNullary is disabled
  private def nonNullaryFilter(d: TlaOperDecl): Boolean = !keepNullary || d.formalParams.nonEmpty
  private def negateFilter(df: DeclFilter): DeclFilter = d => !df(d)

  // Given a declaration (possibly holding a polymorphic type) and a monotyped target, computes
  // a substitution of the two. A substitution is assumed to exist, otherwise TypingException is thrown.
  private def getSubstitution(targetType: TlaType1, decl: TlaOperDecl): (Substitution, TlaType1) = {
    val genericType = decl.typeTag.asTlaType1()
    new TypeUnifier().unify(Substitution.empty, genericType, targetType) match {
      case None =>
        throw new TypingException(
            s"Inliner: Unable to unify generic signature $genericType of ${decl.name} with the concrete type $targetType",
            decl.ID)

      case Some(pair) => pair
    }
  }

  // Assume name is in scope.
  // Creates a fresh copy of the operator body and replaces formal parameter instances with the argument instances.
  private def instantiateWithArgs(scope: Scope)(name: String, args: Seq[TlaEx]): TlaEx = {
    val decl = scope(name)

    // Note: it can happen that the body and the decl have desynced types,
    // due to the way type-checking is currently implemented for polymorphic operators.
    // We fix that below with type unification.
    val freshBody = deepCopy(decl.body)

    // Each formal parameter gets instantiated independently.
    val newBody = decl.formalParams.zip(args).foldLeft(freshBody) { case (partialBody, (fParam, arg)) =>
      val replaced = ReplaceFixed(tracker)(NameEx(fParam.name)(arg.typeTag), arg)(partialBody)
      // Higher-order parameter instantiation warrants a call to transform, since the parameter can get
      // instantiated with either a lambda or a global operator
      if (!fParam.isOperator) replaced
      else transform(scope)(replaced)
    }

    // If the operator has a parametric signature, we have to substitute type parameters with concrete parameters
    // 1. Unify the operator type with the arguments.
    // 2. Apply the resulting substitution to the types in all subexpressions.
    val actualType = OperT1(args.map(_.typeTag.asTlaType1()), freshBody.typeTag.asTlaType1())

    val (substitution, _) = getSubstitution(actualType, decl)

    if (substitution.isEmpty) newBody
    else new TypeSubstitutor(tracker, substitution)(newBody)
  }

  // Assume name is in scope. Creates a local LET-IN for call-by-name operators.
  private def embedCallByName(scope: Scope)(nameEx: NameEx): TlaEx = {
    val decl = scope(nameEx.name)

    // like in instantiateWithArgs, we compare the declaration type to the expected monotype
    val freshBody = deepCopy(decl.body)
    val monoOperType = nameEx.typeTag.asTlaType1()

    val (substitution, tp) = getSubstitution(monoOperType, decl)

    val tpTag = Typed(tp)

    val newBody =
      if (substitution.isEmpty) freshBody
      else new TypeSubstitutor(tracker, substitution)(freshBody)

    // To make a local definition, we use a fresh name
    val newName = nameGenerator.newName()
    val newLocalDecl = TlaOperDecl(newName, decl.formalParams, newBody)(tpTag)

    LetInEx(NameEx(newName)(tpTag), newLocalDecl)(tpTag)
  }

  // Checks for the specific LET-IN form used by LAMBDA and call-by-name
  private def isCallByName(letInEx: LetInEx): Boolean = letInEx match {
    case LetInEx(NameEx(bodyName), TlaOperDecl(operName, _, _)) => operName == bodyName
    case _                                                      => false
  }

  // main access method, performs the transformations described above
  def transform(scope: Scope): TlaExTransformation = tracker.trackEx {
    // Standard application
    case OperEx(TlaOper.apply, NameEx(name), args @ _*) if scope.contains(name) =>
      instantiateWithArgs(scope)(name, args)

    // Roundabout application, happens if you pass a lambda to a HO operator
    case OperEx(TlaOper.apply, LetInEx(NameEx(name), decl @ TlaOperDecl(declName, params, _)), args @ _*)
        if name == declName && params.size == args.size =>
      // not 100% optimal, but much easier to read/maintain: just push the lambda into scope and apply the std case
      val (newScope, _) = pushDeclsIntoScope()(scope, List(decl))
      instantiateWithArgs(newScope)(name, args)

    // LET-IN extends scope
    case letInEx @ LetInEx(body, defs @ _*) =>
      // We never want to remove the definitions from a call-by-name or lambda, so the operator filter depends on whether or not
      // this is a generic LET-IN or a call-by-name
      val filterFun =
        if (isCallByName(letInEx)) FilterFun.ALL
        else negateFilter(nonNullaryFilter)

      val (newScope, remainingOpers) = pushDeclsIntoScope(filterFun)(scope, defs)
      // pushDeclsIntoScope is generic, so it doesn't know all TlaDecl are TlaOperDecl, so we just cast all of them
      val castDecls = remainingOpers.map(_.asInstanceOf[TlaOperDecl])
      val newBody = transform(newScope)(body)

      // If we ended up pushing all declarations into the scope, then we can get rid of toplevel LET-IN
      if (castDecls.isEmpty) newBody
      else LetInEx(newBody, castDecls: _*)(newBody.typeTag)

    // call-by-name
    case nameEx: NameEx if scope.contains(nameEx.name) =>
      embedCallByName(scope)(nameEx)

    // Standard recursive case
    case ex @ OperEx(oper, args @ _*) =>
      OperEx(oper, args.map(transform(scope)): _*)(ex.typeTag)

    // No inlining for non-operator non-name expressions
    case ex => ex
  }

  // Module-level transformation. Guarantees traversal of declarations in dependency order
  override def apply(m: TlaModule): TlaModule = {
    val declSorter = new DeclarationSorter
    // Instead of pre-building a body map, sorts operators according to
    // dependency order and iterates over a sorted collection
    val moduleWithSortedDecls = declSorter(m)

    val sortedDecls = moduleWithSortedDecls.declarations

    // Instead of building a parallel BodyMap, we build scope iteratively, as the declarations are now in order.
    // Because we keep global declarations, we may need to use FilterFun.ALL or a similar filter unrelated to arity
    // Also, because global operators are inlined even if nullary, we force scope filter to be ALL
    val inlinedDecls = pushDeclsIntoScope(toplevelFilter, FilterFun.ALL)(emptyScope, sortedDecls)._2

    m.copy(declarations = inlinedDecls)
  }

}

object Inliner {

  type Scope = BodyMap
  def emptyScope: Scope = Map.empty

  type DeclFilter = TlaOperDecl => Boolean

  object FilterFun {
    def ALL: DeclFilter = _ => true
    def NAMED(set: Set[String]): DeclFilter = d => set.contains(d.name)
  }

}
