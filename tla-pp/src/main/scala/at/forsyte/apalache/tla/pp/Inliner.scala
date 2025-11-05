package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{TlaEx, _}
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.standard.{DeclarationSorter, DeepCopy, IncrementalRenaming, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.pp.Inliner.{DeclFilter, FilterFun}
import at.forsyte.apalache.tla.types.{EqClass, Substitution, TypeUnifier, TypeVarPool}

import scala.collection.immutable.SortedMap

/**
 * Given a module m, with global operators F1,...,Fn, Inliner performs the following transformation:
 *   - For each i, replaces all application instances Fi(a1i, ..., aki) in m, where Fi(p1i,...,pki) == ei, with
 *     ei[a1/p1i, ..., aki/pki]
 *   - Replaces each instance of LET G1(q11,...,qk1) == g1 ... Gm(q1m, ..., qkm) == gm IN f, with:
 *     - f, inlined by the previous rule, as if G1, ..., Gm were global, if `keepNullary` is `false`, or,
 *     - LET Gj1 == gj1 ... Gjl == gjl IN ff, where Gj1, ..., Gjl are all the nullary operators among G1,...,Gm and ff
 *       is the expression obtained by inlining f as though all G1,...,Gm, that are not among Gj1, ..., Gjl, were global
 *   - For each instance of pass-by-name A (where a definition A(p1,...,pk) == e exists in scope), replaces
 *     - A with LET A_LOCAL(p1,...,pk) = e IN A_LOCAL
 *
 * If calling `transformModule`, then `moduleLevelFilter` determines which operator declarations remain in the module
 * after inlining. Default: ALL.
 *
 * @author
 *   Jure Kukovec
 */
class Inliner(
    tracker: TransformationTracker,
    renaming: IncrementalRenaming,
    // Nullary polymorphic operators are _always_ inlined. This flag only governs non-nullary operators. See #1880
    keepNullaryMono: Boolean = true,
    moduleLevelFilter: DeclFilter = FilterFun.ALL) {

  private val deepcopy = DeepCopy(tracker)
  private def deepCopy(ex: TlaEx): TlaEx = renaming(deepcopy.deepCopyEx(ex))

  import Inliner._

  // Return scope extended by decl if decl is non-recursive and passes scopeFilter. Used for bookkeeping below.
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
  // Operator declarations are added to the scope if they satisfy scopeFilter and kept in the declaration list if they satisfy
  // operDeclFilter. By default, operDeclFilter = !nonNullaryFilter, scopeFilter = nonNullaryFilter
  private def pushDeclsIntoScope(
      operDeclFilter: DeclFilter = negateFilter(nonNullaryFilter),
      scopeFilter: DeclFilter = nonNullaryFilter,
    )(initialScope: Scope,
      decls: Iterable[TlaDecl]): (Scope, List[TlaDecl]) =
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
        // For theorems and assumptions, just apply tx, no scope modifications
        case theoremDecl: TlaTheoremDecl =>
          val newBody = transform(scope)(theoremDecl.body)
          val newDecl = tracker.trackDecl { _ => theoremDecl.copy(body = newBody)(theoremDecl.typeTag) }(theoremDecl)
          (scope, decls :+ newDecl)
        case assumeDecl: TlaAssumeDecl =>
          val newBody = transform(scope)(assumeDecl.body)
          val newDecl = tracker.trackDecl { _ => assumeDecl.copy(body = newBody)(assumeDecl.typeTag) }(assumeDecl)
          (scope, decls :+ newDecl)
        case _ => (scope, decls :+ decl)
      }
    }

  // Lifts TlaType1.isMono to tags
  private def isPolyTag(tag: TypeTag) = tag match {
    case Typed(tlaType1: TlaType1) => !tlaType1.isMono
    case _                         => false
  }

  // Default scope filter, we add nullary operators if keepNullaryMono is disabled or if they're polymorphic
  private def nonNullaryFilter(d: TlaOperDecl): Boolean =
    !keepNullaryMono || isPolyTag(d.typeTag) || d.formalParams.nonEmpty

  // Given a declaration `callee` (possibly holding a polymorphic type) and the type at a call site,
  // which can also be a polytype, computes a substitution of the two. A substitution is assumed to exist,
  // otherwise TypingException is thrown.
  private def getSubstitution(callSiteType: TlaType1, callee: TlaOperDecl): (Substitution, TlaType1) = {
    val calleeType = callee.typeTag.asTlaType1()
    // To fix transitive inlining of polymorphic operators, rename all type variables in `callee`
    // to fresh ones, so these type variables have indices larger than those in `callSiteType`.
    // The unification algorithm prefers to keep type variables with smaller indices,
    // so this ensures that type variables from `callSiteType` are kept.
    // See the issue #3204.
    val maxUsedVar = ((calleeType.usedNames ++ callSiteType.usedNames) ++ Set(0)).max
    val typeVarPool = new TypeVarPool(maxUsedVar + 1)
    val calleeSub = Substitution(calleeType.usedNames.map(v => EqClass(v) -> typeVarPool.fresh).toMap)
    val calleeTypeRenamed = calleeSub.subRec(calleeType)

    new TypeUnifier(typeVarPool).unify(Substitution.empty, callSiteType, calleeTypeRenamed) match {
      case None =>
        throw new TypingException(s"Inliner: Unable to unify the signature $calleeType of ${callee.name} "
              + "with the type $callSiteType at call site", callee.ID)

      case Some((unifierSub, unifiedType)) =>
        // Now, we have to add the renamed type variables back to the substitution.
        // To this end, we compose `calleeSub` with `unifierSub`.
        // Not that we are not merging them. Otherwise, the type variables of `callee` might take over.
        val composed = Substitution(calleeSub.mapping ++ unifierSub.mapping)
        (composed, composed.subRec(unifiedType))
    }
  }

  // Assume an operator declaration named `name` is in scope.
  // Creates a fresh copy of the operator body and replaces formal parameter instances with the argument instances.
  private def instantiateWithArgs(scope: Scope)(nameEx: NameEx, args: Seq[TlaEx]): TlaEx = {
    val name = nameEx.name
    val callee = scope(name)

    val freshBody = deepCopy(callee.body)

    // All formal parameters get instantiated at once, to avoid parameter-name issues, see #1903
    val paramMap = callee.formalParams
      .zip(args)
      .map({ case (OperParam(name, _), arg) =>
        name -> arg
      })
      .toMap

    val replacedBody = ReplaceFixed(tracker).withFun {
      case NameEx(name) if paramMap.contains(name) => paramMap(name)
    }(freshBody)

    // There are two cases where the above instantiation might be incomplete:
    // a) In the case of an application of the form A(B()), `arg` will have the value `B()`, which is _not_
    //    a fully inlined expression
    // b) In the case of an application of the form A(B), where A is a HO operator and `B` is an operator name
    //    Then, if A(F(_)) == e, e[B/F] would contain applications of the form B(...), which are _not_ fully inlined.
    //    Note that `F` cannot be higher-order itself, by the rules of TLA+.
    // To cover both cases at once, we run an additional transform on the replaced body
    val newBody = transform(scope)(replacedBody)

    // Note: it can happen that the type at the call site and the type of `callee` have different types,
    // e.g., the `callee` has a more general polytype, or they are both polytypes.
    // We fix that below with type unification:
    //  1. Unify the operator type with the arguments.
    //  2. Apply the resulting substitution to the types in all subexpressions.
    //  3. Importantly, we prefer the type variables of the call site, as they are the type variables of
    //     the caller context.
    val callSiteType = nameEx.typeTag.asTlaType1()

    val (substitution, _) = getSubstitution(callSiteType, callee)

    if (substitution.isEmpty) newBody
    else new TypeSubstitutor(tracker, substitution)(newBody)
  }

  // Assume name is in scope. Creates a local LET-IN for pass-by-name operators.
  private def embedPassByName(scope: Scope)(nameEx: NameEx): TlaEx = {
    val callee = scope(nameEx.name)

    // like in instantiateWithArgs, we compare the declaration type to the expected monotype
    val freshBody = deepCopy(callee.body)
    val monoOperType = nameEx.typeTag.asTlaType1()

    val (substitution, tp) = getSubstitution(monoOperType, callee)

    val tpTag = Typed(tp)

    val newBody =
      if (substitution.isEmpty) freshBody
      else new TypeSubstitutor(tracker, substitution)(freshBody)

    // To make a local definition, we use a fresh name, derived from the original name, but renamed to get a fresh $N
    val newName = renaming.apply(NameEx(callee.name)(callee.typeTag)).asInstanceOf[NameEx].name
    val newLocalDecl = TlaOperDecl(newName, callee.formalParams, newBody)(tpTag)

    LetInEx(NameEx(newName)(tpTag), newLocalDecl)(tpTag)
  }

  def transformEx: TlaExTransformation = transform(emptyScope)

  // main access method, performs the transformations described above
  def transform(scope: Scope): TlaExTransformation = tracker.trackEx {
    // Standard application
    case OperEx(TlaOper.apply, nameEx @ NameEx(name), args @ _*) if scope.contains(name) =>
      instantiateWithArgs(scope)(nameEx, args)

    // Roundabout application, happens if you pass a lambda to a HO operator
    case OperEx(TlaOper.apply, LetInEx(nameEx @ NameEx(name), decl @ TlaOperDecl(declName, params, _)), args @ _*)
        if name == declName && params.size == args.size =>
      // Easiest to read/maintain: just push the lambda into scope and apply the std case
      val (newScope, _) = pushDeclsIntoScope()(scope, List(decl))
      instantiateWithArgs(newScope)(nameEx, args)

    // LET-IN extends scope
    case letInEx @ LetInEx(body, defs @ _*) =>
      // Depending on whether this is an instance of pass-by-name/lambda, we have two considerations:
      // 1) We never want to remove the definitions from a pass-by-name or lambda, so the operator filter depends on
      // whether or not this is a generic LET-IN or a pass-by-name
      // 2) As `transform` also embeds pass-by-names, we don't want to embed an already embedded pass-by-name
      val (filterFun, bodyTx): (DeclFilter, (Scope, TlaEx) => TlaEx) =
        if (isPassByName(letInEx))
          (FilterFun.ALL, { case (_, e) => e }) // (ALL, NO-OP)
        else
          (negateFilter(nonNullaryFilter), { case (s, e) => transform(s)(e) }) // (!NULLARY, transform)

      val (newScope, remainingOpers) = pushDeclsIntoScope(filterFun)(scope, defs)
      // pushDeclsIntoScope is generic, so it doesn't know all TlaDecl are TlaOperDecl, so we just cast all of them
      val castDecls = remainingOpers.map(_.asInstanceOf[TlaOperDecl])
      // if we know this is already a pass-by name, no need to re-embed, since body must be a NameEx
      // In this case newBody = body
      val newBody = bodyTx(newScope, body)

      // If we ended up pushing all declarations into the scope, then we can get rid of toplevel LET-IN
      if (castDecls.isEmpty) newBody
      else LetInEx(newBody, castDecls: _*)(newBody.typeTag)

    // pass-by-name
    case nameEx: NameEx if scope.contains(nameEx.name) =>
      embedPassByName(scope)(nameEx)

    // Standard recursive case
    case ex @ OperEx(oper, args @ _*) =>
      OperEx(oper, args.map(transform(scope)): _*)(ex.typeTag)

    // No inlining for non-operator non-name expressions
    case ex => ex
  }

  // Module-level transformation. Guarantees traversal of declarations in dependency order
  def transformModule(m: TlaModule): TlaModule = {
    val declSorter = new DeclarationSorter
    // Instead of pre-building a body map, sorts operators according to
    // dependency order and iterates over a sorted collection
    val moduleWithSortedDecls = declSorter(m)

    val sortedDecls = moduleWithSortedDecls.declarations

    // Instead of building a parallel BodyMap, we build scope iteratively, as the declarations are now in order.
    // Because we keep global declarations, we may need to use FilterFun.ALL or a similar filter unrelated to arity
    // Also, because global operators are inlined even if nullary, we force scope filter to be ALL
    val inlinedDecls = pushDeclsIntoScope(moduleLevelFilter, FilterFun.ALL)(emptyScope, sortedDecls)._2

    m.copy(declarations = inlinedDecls)
  }

}

object Inliner {

  type Scope = BodyMap
  def emptyScope: Scope = SortedMap.empty

  type DeclFilter = TlaOperDecl => Boolean

  def negateFilter(df: DeclFilter): DeclFilter = d => !df(d)

  object FilterFun {
    def ALL: DeclFilter = _ => true
    def RESTRICT_TO(names: Set[String]): DeclFilter = d => names.contains(d.name)
  }

  // Checks for the specific LET-IN form used by LAMBDA and pass-by-name
  def isPassByName(letInEx: LetInEx): Boolean = letInEx match {
    case LetInEx(NameEx(bodyName), TlaOperDecl(operName, _, _)) => operName == bodyName
    case _                                                      => false
  }

}
