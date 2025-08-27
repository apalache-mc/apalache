package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types._
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.etc.EtcTypeChecker.UnwindException
import scalaz.unused

/**
 * ETC: Embarrassingly simple Type Checker.
 *
 * @param varPool
 *   a pool of fresh variables
 * @param inferPolytypes
 *   whether the type checker is allowed to compute polymorphic types of user-defined operators.
 * @author
 *   Igor Konnov
 */
class EtcTypeChecker(varPool: TypeVarPool, inferPolytypes: Boolean = true) extends TypeChecker with EtcBuilder {
  private var listener: TypeCheckerListener = new DefaultTypeCheckerListener()

  /**
   * Compute the expression type in a type context. If the expression is not well-typed, return None. As a side effect,
   * call the listener, when discovering new types or errors.
   *
   * @param typeListener
   *   a listener that will receive the type error or type info
   * @param rootCtx
   *   a typing context
   * @param rootEx
   *   an expression
   * @return
   *   Some(type), if the expression is well-typed; and None otherwise.
   */
  override def compute(typeListener: TypeCheckerListener, rootCtx: TypeContext, rootEx: EtcExpr): Option[TlaType1] = {
    listener = typeListener // set the type listener, so we do not have to pass it around

    // The types are computed in operator applications, add extra tests and listener calls for non-operators
    try {
      val rootSolver = new ConstraintSolver(varPool)
      // The whole expression has been processed. Compute the type of the expression.
      val rootType = computeRec(rootCtx, rootSolver, rootEx)
      rootSolver.solve() match {
        case None =>
          onTypeError(rootEx.sourceRef, s"Error when computing the type of the top expression")
          None

        case Some(sub) =>
          val exactType = sub.subRec(rootType)
          onTypeFound(rootEx.sourceRef, exactType)
          Some(exactType)
      }

    } catch {
      case _: UnwindException =>
        // the type checker has flagged a type error down in the syntax tree
        None
    }
  }

  private def computeRec(ctx: TypeContext, solver: ConstraintSolver, ex: EtcExpr): TlaType1 = {
    ex match {
      case EtcConst(polytype) =>
        // A constant type, either monotype or polytype.
        // add the constraint: x = polytype, for a fresh x
        val fresh = varPool.fresh
        val clause = EqClause(fresh, polytype)
          .setOnTypeFound(tt => onTypeFound(ex.sourceRef, tt))
          .setOnTypeError((_, _) => onTypeError(ex.sourceRef, "Unresolved type"))
        solver.addConstraint(clause)
        fresh

      case EtcTypeDecl(name: String, declaredType: TlaType1, scopedEx: EtcExpr) =>
        // An inline type annotation.
        // Just propagate the annotated name down the tree. It will be used in a let definition.
        // All free type variables in the type are considered to be universally quantified.
        val polyVars = declaredType.usedNames
        val extCtx = new TypeContext(ctx.types + (name -> TlaType1Scheme(declaredType, polyVars)))
        if (polyVars.isEmpty) {
          // For a non-polymorphic type, report it, as it may be the only place, where it is reported.
          // This is relevant for VARIABLES and CONSTANTS.
          // Add a trivial constraint: a = declaredType. We need it to place a callback.
          val fresh = varPool.fresh
          val watchClause =
            EqClause(fresh, declaredType)
              .setOnTypeFound { inferredType =>
                onTypeFound(ex.sourceRef, inferredType)
              }
          solver.addConstraint(watchClause)
        }

        computeRec(extCtx, solver, scopedEx)

      case EtcName(name) =>
        // a variable name, either an operator name, or a variable introduced by lambda (EtcAbs)
        if (ctx.types.contains(name)) {
          val scheme = ctx.types(name)
          if (scheme.principalType.usedNames.isEmpty) {
            // This is a monotype. Report it right away.
            onTypeFound(ex.sourceRef, scheme.principalType)
            scheme.principalType
          } else {
            // introduce a constant, as the type may get refined later
            computeRec(ctx, solver, mkConst(ex.sourceRef, scheme.principalType))
          }
        } else {
          onTypeError(ex.sourceRef, s"No annotation found for $name. Make sure that you've put one in front of $name.")
          throw new UnwindException
        }

      case appEx @ EtcApp(operTypes, args @ _*) =>
        // Application by type.
        // Apply toList first, in case `args` is a stream. The reason is that `computeRec` introduces side effects
        val argTypes = args.toList.map(arg => computeRec(ctx, solver, arg))
        val resVar = varPool.fresh
        val operVar = varPool.fresh

        def onFound: TlaType1 => Unit = {
          case OperT1(_, res) =>
            // report the result of operator application, not the operator type itself
            onTypeFound(ex.sourceRef, res)

          case _ =>
            throw new TypingException("Expected an operator type, found: ", appEx.sourceRef.tlaId)
        }

        def onOverloadingError(sub: Substitution, signatures: Seq[TlaType1]): Unit = {
          // The constraint solver has failed to solve the disjunctive clause:
          // operVar = operType_1 \/ ... \/ operVar = operType_n
          val evalArgTypes = argTypes.map(sub.subRec)
          val argOrArgs = pluralArgs(argTypes.length)
          if (signatures.isEmpty) {
            onTypeError(appEx.sourceRef, s"No matching signature for $argOrArgs $evalArgTypes")
          } else {
            // it should be the case that manySigs has at least two elements, but we also include the case of one
            val sepSigs = String.join(" or ", signatures.map(_.toString()): _*)
            val defaultMessage =
              s"Annotation required. Found ${signatures.length} matching operator signatures $sepSigs for $argOrArgs ${evalArgTypes
                  .mkString(" and ")}"
            val specificMessage = appEx.explain(signatures.toList, evalArgTypes)
            onTypeError(appEx.sourceRef, if (specificMessage.isDefined) specificMessage.get else defaultMessage)
          }
        }

        def onArgsMatchError(sub: Substitution, @unused types: Seq[TlaType1]): Unit = {
          // no solution for: operVar = (arg_1, ..., arg_k) => resVar
          val evalArgTypes = argTypes.map(sub.subRec)
          val argOrArgs = pluralArgs(argTypes.length)
          val evalSig = sub.subRec(operVar)
          val defaultMessage =
            s"An operator with the signature $evalSig cannot be applied to the provided $argOrArgs of type ${evalArgTypes
                .mkString(" and ")}"
          val specificMessage = appEx.explain(List(evalSig), evalArgTypes)
          onTypeError(appEx.sourceRef, if (specificMessage.isDefined) specificMessage.get else defaultMessage)
        }

        // operVar = (arg_1, ..., arg_k) => resVar
        solver.addConstraint(EqClause(operVar, lir.OperT1(argTypes, resVar))
              .setOnTypeFound(onFound)
              .setOnTypeError(onArgsMatchError))

        def onSigMatchError(sub: Substitution, sigs: Seq[TlaType1]): Unit = {
          // no solution for: operVar = operType_1
          val evalArgTypes = argTypes.map(sub.subRec)
          val argOrArgs = pluralArgs(argTypes.length)
          val evalSig = sigs.head
          val defaultMessage =
            s"An operator with the signature $evalSig cannot be applied to the provided $argOrArgs of type ${evalArgTypes
                .mkString(" and ")}"
          val specificMessage = appEx.explain(List(evalSig), evalArgTypes)
          onTypeError(appEx.sourceRef, if (specificMessage.isDefined) specificMessage.get else defaultMessage)
        }

        if (operTypes.length == 1) {
          // the common case, which should be solved without using OrClause (which can be postponed):
          // operVar = operType_1
          solver.addConstraint(EqClause(operVar, operTypes.head).setOnTypeError(onSigMatchError))
        } else {
          // the case of overloaded operators:
          // operVar = operType_1 \/ ... \/ operVar = operType_n
          solver.addConstraint(OrClause(operTypes.map(EqClause(operVar, _)): _*)
                .setOnTypeError(onOverloadingError)
                .asInstanceOf[OrClause])
        }

        // the expected result is stored in resVar
        resVar

      // Operator application by name. Resolve the name and pass the resolved expression to the application case.
      case EtcAppByName(name, args @ _*) =>
        // application by name
        if (ctx.types.contains(name.name)) {
          val scheme = ctx.types(name.name)
          var instantiatedType = scheme.principalType
          if (scheme.quantifiedVars.nonEmpty) {
            // The type is parametric: instantiate it with new type variables.
            val varRenamingMap = scheme.quantifiedVars.toSeq.map(v => EqClass(v) -> varPool.fresh)
            instantiatedType = Substitution(varRenamingMap: _*).subRec(scheme.principalType)
          }

          // If we reported the type right away, it would contained variables that have not been resolved yet.
          // Hence, we introduce a fresh variable to get the type reported, once the solver knows it most precisely.
          val fresh = varPool.fresh
          val clause = EqClause(fresh, instantiatedType)
            .setOnTypeFound(tt => onTypeFound(name.sourceRef, tt))
          solver.addConstraint(clause)
          // delegate the rest to the application-by-type
          val instantiatedExpr = mkApp(ex.sourceRef, Seq(instantiatedType), args: _*)
          instantiatedExpr.typeErrorExplanation = ex.typeErrorExplanation

          computeRec(ctx, solver, instantiatedExpr)
        } else {
          onTypeError(ex.sourceRef, s"The operator $name is used before it is defined.")
          throw new UnwindException
        }

      case EtcAbs(scopedEx, binders @ _*) =>
        // lambda x \in e1, y \in e2, ...: scopedEx
        val extCtx = translateBinders(ctx, solver, binders)
        // compute the expression in the scope
        val underlyingType = computeRec(extCtx, solver, scopedEx)
        // introduce a variable for lambda, in order to propagate the type to the listener
        val lambdaTypeVar = varPool.fresh
        val varNames = binders.map { case (name, _) => extCtx(name.name).principalType }
        val operType = OperT1(varNames, underlyingType)
        // lambdaTypeVar = (a_1, ..., a_k) => resType
        val lambdaClause = EqClause(lambdaTypeVar, operType)
          .setOnTypeFound(tt => onTypeFound(ex.sourceRef, tt))
          .setOnTypeError((_, ts) =>
            onTypeError(ex.sourceRef.asInstanceOf[ExactRef], "Type error in parameters: " + ts.head))
        solver.addConstraint(lambdaClause)
        operType

      case letEx @ EtcLet(name, defEx @ EtcAbs(defBody, binders @ _*), scopedEx) =>
        // Let-definitions that support polymorphism.
        // let name = lambda x \in X, y \in Y, ...: boundEx in scopedEx
        // Before analyzing the operator definition, try to partially solve the equations in the current context.
        // If it is successful, use the partial solution to refine the types in the type context.
        val approxSolution = solver.solvePartially().getOrElse(throw new UnwindException)

        // introduce a new instance of the constraint solver for the operator definition
        val letInSolver = new ConstraintSolver(varPool)
        val operScheme =
          ctx.types.get(name) match {
            case Some(scheme @ TlaType1Scheme(OperT1(_, _), _)) =>
              scheme

            case Some(TlaType1Scheme(someType: TlaType1, allVars)) =>
              // The definition has a type annotation which is not an operator. Assume it is a nullary operator.
              // Strictly speaking, this is a hack. However, it is quite common to declare a constant with LET.
              TlaType1Scheme(OperT1(Seq(), someType), allVars)

            case None =>
              // Let the solver compute the type. If it fails, the user has to annotate the definition
              val freshArgs = 1.to(binders.length).map(_ => varPool.fresh)
              val freshRes = varPool.fresh
              val freeVars = (freshArgs :+ freshRes).map(_.no).toSet
              TlaType1Scheme(lir.OperT1(freshArgs, freshRes), freeVars)
          }

        // translate the binders in the lambda expression, so we can quickly propagate the types of the parameters
        val preCtx =
          new TypeContext((ctx.types + (name -> operScheme)).view
                .mapValues(p => p.copy(approxSolution.subRec(p.principalType)))
                .toMap)
        val extCtx = translateBinders(preCtx, letInSolver, binders)
        val annotationParams = operScheme.principalType.asInstanceOf[OperT1].args
        annotationParams.zip(binders.map { case (pname, _) => (pname, extCtx(pname.name).principalType) }).foreach {
          case (annotParam, (pname, paramVar @ VarT1(_))) =>
            val clause = EqClause(paramVar, annotParam)
              .setOnTypeError((_, ts) => s"Mismatch in parameter $pname. Found: " + ts.head)
            letInSolver.addConstraint(clause)

          case b =>
            throw new IllegalStateException("Unexpected binder: " + b)
        }

        // produce constraints for the operator signature
        def onError(sub: Substitution, ts: Seq[TlaType1]): Unit = {
          val sepSigs = String.join(" and ", ts.map(t => sub.subRec(t).toString): _*)
          onTypeError(defEx.sourceRef, s"Expected ${sub.subRec(operScheme.principalType)} in $name. Found: $sepSigs")
        }

        val operVar = varPool.fresh
        // Importantly, do not report the type of `defEx` as soon as it is found.
        // The variables in the `defEx` may change when we apply the substitution later.
        val sigClause = EqClause(operVar, operScheme.principalType)
          .setOnTypeError(onError)
        letInSolver.addConstraint(sigClause)

        // compute the constraints for the operator definition
        val defBodyType = computeRec(extCtx, letInSolver, defBody)
        val paramTypes = binders.map(p => extCtx(p._1.name).principalType)
        val defType = OperT1(paramTypes, defBodyType)
        // add the constraint from the annotation
        val defClause = EqClause(operVar, defType)
          .setOnTypeError(onError)

        letInSolver.addConstraint(defClause)

        val principalDefType =
          letInSolver.solve() match {
            case None =>
              onTypeError(ex.sourceRef, s"Error when computing the type of $name")
              throw new UnwindException

            case Some(sub) =>
              sub.subRec(defType)
          }

        // Find free variables of the principal type, to use them as quantified variables
        val freeVars = principalDefType.usedNames.filter(solver.isFreeVar)
        if (!inferPolytypes && freeVars.nonEmpty) {
          // the user has disabled let-polymorphism
          onTypeError(ex.sourceRef,
              s"Operator $name has a parameterized type, while polymorphism is disabled: " + principalDefType)
          throw new UnwindException
        }

        // If the operator is annotated, compare the annotation with the inferred type.
        // If the type annotation is more general than the inferred principal type, report an error.
        if (ctx.types.contains(name)) {
          val inferredType = principalDefType
          val userType = operScheme.principalType
          new TypeUnifier(varPool).unify(Substitution(), inferredType, userType) match {
            case None =>
              val msg = s"Contradiction in the type solver: $inferredType and $userType should be unifiable"
              throw new TypingException(msg, letEx.sourceRef.tlaId)

            case Some((_, unifiedType)) =>
              if (unifiedType.usedNames.size < operScheme.principalType.usedNames.size) {
                // The number of free variables has decreased. The annotation by the user is too general.
                val msg = s"$name's type annotation $userType is too general, inferred: $inferredType"
                onTypeWarn(letEx.sourceRef, msg)
              }
          }
        }

        // report the type of the definition
        onTypeFound(defEx.sourceRef, principalDefType)

        // compute the type of the expression under the definition
        val underCtx = new TypeContext(ctx.types + (name -> TlaType1Scheme(principalDefType, freeVars)))
        computeRec(underCtx, solver, scopedEx)

      // an ill-formed let expression
      case EtcLet(_, _, _) =>
        throw new RuntimeException("Bug in type checker. Ill-formed let-expression: " + ex)
    }
  }

  // produce constraints for the binders that are used in a lambda expression
  private def translateBinders(
      ctx: TypeContext,
      solver: ConstraintSolver,
      binders: Seq[(EtcName, EtcExpr)]): TypeContext = {
    // Apply `toList` first, in case `binders` is lazy. Because `computeRec` has side effects.
    val setTypes = binders.toList.map(binder => computeRec(ctx, solver, binder._2))
    // introduce type variables b_1, ..., b_k for the binding sets
    val setVars = 1.to(binders.size).map(_ => varPool.fresh)
    // ...and type variables a_1, ..., a_k for the set elements
    val elemVars = 1.to(binders.size).map(_ => varPool.fresh)
    // require that these type variables capture the sets: b_i = Set(a_i) for 1 <= i <= k
    binders.zip(setVars.zip(elemVars)).foreach { case ((_, setEx), (setVar, elemVar)) =>
      val clause = EqClause(setVar, SetT1(elemVar))
        .setOnTypeFound(onTypeFound(setEx.sourceRef, _))
        .setOnTypeError((_, ts) => onTypeError(setEx.sourceRef, "Expected a set. Found: " + ts.head))
      solver.addConstraint(clause)
    }
    // require that these type variables are equal to the computed set types
    binders.zip(setVars.zip(setTypes)).foreach { case ((_, setEx), (setVar, setType)) =>
      val clause = EqClause(setVar, setType)
        .setOnTypeError((_, ts) => onTypeError(setEx.sourceRef, "Expected a set. Found: " + ts.head))
      solver.addConstraint(clause)
    }
    // introduce identity constraints to retrieve the types of the names
    binders.zip(elemVars).foreach { case ((name, _), typeVar) =>
      val clause = EqClause(typeVar, typeVar).setOnTypeFound(onTypeFound(name.sourceRef, _))
      solver.addConstraint(clause)
    }
    // Compute the expression in the scope, by associating the variables names with the elements of elemVars.
    // Note that elemVars are not universally quantified.
    val varNames = binders.map(_._1.name).zip(elemVars.map(TlaType1Scheme(_, Set.empty)))
    new TypeContext(ctx.types ++ varNames)
  }

  private def onTypeFound(sourceRef: EtcRef, tt: TlaType1): Unit = {
    sourceRef match {
      case ref: ExactRef =>
        listener.onTypeFound(ref, tt)

      case _ =>
    }
  }

  private def onTypeError(sourceRef: EtcRef, message: String): Unit = {
    listener.onTypeError(sourceRef, message)
  }

  private def onTypeWarn(sourceRef: EtcRef, message: String): Unit = {
    listener.onTypeWarn(sourceRef, message)
  }

  // Pluralize the string "argument"
  private def pluralArgs(count: Int): String = {
    if (count != 1) "arguments" else "argument"
  }
}

object EtcTypeChecker {

  /**
   * We use this exception to quickly unwind the search stack
   */
  protected class UnwindException extends RuntimeException
}
