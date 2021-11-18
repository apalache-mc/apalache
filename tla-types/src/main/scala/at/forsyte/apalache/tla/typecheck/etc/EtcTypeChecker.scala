package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir
import at.forsyte.apalache.tla.lir.{OperT1, SetT1, TlaType1, TypingException, VarT1}
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.etc.EtcTypeChecker.UnwindException

/**
 * ETC: Embarrassingly simple Type Checker.
 *
 * @param varPool        a pool of fresh variables
 * @param inferPolytypes whether the type checker is allowed to compute polymorphic types of user-defined operators.
 * @author Igor Konnov
 */
class EtcTypeChecker(varPool: TypeVarPool, inferPolytypes: Boolean = true) extends TypeChecker with EtcBuilder {
  private var listener: TypeCheckerListener = new DefaultTypeCheckerListener()

  /**
   * Compute the expression type in a type context. If the expression is not well-typed, return None.
   * As a side effect, call the listener, when discovering new types or errors.
   *
   * @param typeListener a listener that will receive the type error or type info
   * @param rootCtx      a typing context
   * @param rootEx       an expression
   * @return Some(type), if the expression is well-typed; and None otherwise.
   */
  override def compute(typeListener: TypeCheckerListener, rootCtx: TypeContext, rootEx: EtcExpr): Option[TlaType1] = {
    listener = typeListener // set the type listener, so we do not have to pass it around

    // The types are computed in operator applications, add extra tests and listener calls for non-operators
    try {
      val rootSolver = new ConstraintSolver
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
        // All free type variables in the type are considered to be universally quantified,
        val polyVars = declaredType.usedNames
        val extCtx = new TypeContext(ctx.types + (name -> (declaredType, polyVars)))
        if (polyVars.isEmpty) {
          // A non-generic type.
          // For example, it can be a type of a constant, a state variable, or of a concrete operator.
          // To register the type with the type listener, add the trivial constraint: a = declaredType.
          // Importantly, we do not add the callback for parametric types, as their quantified variables may change
          // in the course of type inference.
          // This is sound, because parametric types are reported in the case of `EtcLet`.
          // Yet, we have to report the concrete types here, as they may never appear again down the tree.
          val fresh = varPool.fresh
          val clause = EqClause(fresh, declaredType)
            .setOnTypeFound(tt => onTypeFound(ex.sourceRef, tt))
          solver.addConstraint(clause)
        }

        computeRec(extCtx, solver, scopedEx)

      case EtcName(name) =>
        // a variable name, either an operator name, or a variable introduced by lambda (EtcAbs)
        if (ctx.types.contains(name)) {
          val (knownType, _) = ctx.types(name)
          if (knownType.usedNames.isEmpty) {
            // This is a monotype. Report it right away.
            onTypeFound(ex.sourceRef, knownType)
            knownType
          } else {
            // introduce a constant, as the type may get refined later
            computeRec(ctx, solver, mkConst(ex.sourceRef, knownType))
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

          case tt =>
            throw new TypingException("Expected an operator type, found: " + tt)
        }

        def onOverloadingError(sub: Substitution, signatures: Seq[TlaType1]): Unit = {
          // The constraint solver has failed to solve the disjunctive clause:
          // operVar = operType_1 \/ ... \/ operVar = operType_n
          val evalArgTypes = argTypes.map(sub.subRec).mkString(" and ")
          val argOrArgs = pluralArgs(argTypes.length)
          if (signatures.isEmpty) {
            onTypeError(appEx.sourceRef, s"No matching signature for $argOrArgs $evalArgTypes")
          } else {
            // it should be the case that manySigs has at least two elements, but we also include the case of one
            val sepSigs = String.join(" or ", signatures.map(_.toString()): _*)
            onTypeError(appEx.sourceRef,
                s"Need annotation. Found ${signatures.length} matching operator signatures $sepSigs for $argOrArgs $evalArgTypes")
          }
        }

        def onArgsMatchError(sub: Substitution, types: Seq[TlaType1]): Unit = {
          // no solution for: operVar = (arg_1, ..., arg_k) => resVar
          val evalArgTypes = argTypes.map(sub.subRec).mkString(" and ")
          val argOrArgs = pluralArgs(argTypes.length)
          val evalSig = sub.subRec(operVar)
          onTypeError(appEx.sourceRef, s"No match between operator signature $evalSig and $argOrArgs $evalArgTypes")
        }

        // operVar = (arg_1, ..., arg_k) => resVar
        solver.addConstraint(EqClause(operVar, lir.OperT1(argTypes, resVar))
              .setOnTypeFound(onFound)
              .setOnTypeError(onArgsMatchError))

        def onSigMatchError(sub: Substitution, sigs: Seq[TlaType1]): Unit = {
          // no solution for: operVar = operType_1
          val evalArgTypes = argTypes.map(sub.subRec).mkString(" and ")
          val argOrArgs = pluralArgs(argTypes.length)
          val evalSig = sigs.head
          onTypeError(appEx.sourceRef, s"No match between operator signature $evalSig and $argOrArgs $evalArgTypes")
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
          var (nameType, allVars) = ctx.types(name.name)
          if (allVars.nonEmpty) {
            // The type is parametric: instantiate it with new type variables.
            val varRenamingMap = allVars.toSeq.map(v => EqClass(v) -> varPool.fresh)
            nameType = Substitution(varRenamingMap: _*).subRec(nameType)
          }

          // If we reported the type right away, it would contained variables that have not been resolved yet.
          // Hence, we introduce a fresh variable to get the type reported, once the solver knows it most precisely.
          val fresh = varPool.fresh
          val clause = EqClause(fresh, nameType)
            .setOnTypeFound(tt => onTypeFound(name.sourceRef, tt))
          solver.addConstraint(clause)
          // delegate the rest to the application-by-type
          computeRec(ctx, solver, mkApp(ex.sourceRef, Seq(nameType), args: _*))
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
        val varNames = binders.map { case (name, _) => extCtx(name.name)._1 }
        val operType = OperT1(varNames, underlyingType)
        // lambdaTypeVar = (a_1, ..., a_k) => resType
        val lambdaClause = EqClause(lambdaTypeVar, operType)
          .setOnTypeFound(tt => onTypeFound(ex.sourceRef, tt))
          .setOnTypeError((_, ts) =>
            onTypeError(ex.sourceRef.asInstanceOf[ExactRef], "Type error in parameters: " + ts.head)
          )
        solver.addConstraint(lambdaClause)
        operType

      case EtcLet(name, defEx @ EtcAbs(defBody, binders @ _*), scopedEx) =>
        // Let-definitions that support polymorphism.
        // let name = lambda x \in X, y \in Y, ...: boundEx in scopedEx
        // Before analyzing the operator definition, try to partially solve the equations in the current context.
        // If it is successful, use the partial solution to refine the types in the type context.
        val approxSolution = solver.solvePartially().getOrElse(throw new UnwindException)

        // introduce a new instance of the constraint solver for the operator definition
        val letInSolver = new ConstraintSolver()
        val (operSig, operAllVars) =
          ctx.types.get(name) match {
            case Some((declaredType @ OperT1(_, _), allVars)) =>
              (declaredType, allVars)

            case Some((someType: TlaType1, allVars)) =>
              // The definition has a type annotation which is not an operator. Assume it is a nullary operator.
              // Strictly speaking, this is a hack. However, it is quite common to declare a constant with LET.
              (OperT1(Seq(), someType), allVars)

            case None =>
              // Let the solver compute the type. If it fails, the user has to annotate the definition
              val freshArgs = 1.to(binders.length).map(_ => varPool.fresh)
              val freshRes = varPool.fresh
              val freeVars = (freshArgs :+ freshRes).map(_.no).toSet
              (lir.OperT1(freshArgs, freshRes), freeVars)
          }

        // translate the binders in the lambda expression, so we can quickly propagate the types of the parameters
        val preCtx =
          new TypeContext((ctx.types + (name -> (operSig, operAllVars)))
                .mapValues(p => (approxSolution.subRec(p._1), p._2)))
        val extCtx = translateBinders(preCtx, letInSolver, binders)
        val annotationParams = operSig.args
        annotationParams.zip(binders.map { case (pname, _) => (pname, extCtx(pname.name)._1) }).foreach {
          case (annotParam, (pname, paramVar @ VarT1(_))) =>
            val clause = EqClause(paramVar, annotParam)
              .setOnTypeError((_, ts) => s"Mismatch in parameter $pname. Found: " + ts.head)
            letInSolver.addConstraint(clause)

          case b =>
            throw new IllegalStateException("Unexpected binder: " + b)
        }

        // produce constraints for the operator signature
        def onError(sub: Substitution, ts: Seq[TlaType1]): Unit = {
          val sepSigs = String.join(" and ", ts.map(_.toString()): _*)
          onTypeError(defEx.sourceRef, s"Expected $operSig in $name. Found: $sepSigs")
        }

        val operVar = varPool.fresh
        // Importantly, do not report the type of `defEx` as soon as it is found.
        // The variables in the `defEx` may change when we apply the substitution later.
        val sigClause = EqClause(operVar, operSig)
          .setOnTypeError(onError)
        letInSolver.addConstraint(sigClause)

        // compute the constraints for the operator definition
        val defBodyType = computeRec(extCtx, letInSolver, defBody)
        val paramTypes = binders.map(p => extCtx(p._1.name)._1)
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

        // report the type of the definition
        onTypeFound(defEx.sourceRef, principalDefType)

        // compute the type of the expression under the definition
        val underCtx = new TypeContext(ctx.types + (name -> (principalDefType, freeVars)))
        computeRec(underCtx, solver, scopedEx)

      // an ill-formed let expression
      case EtcLet(_, _, _) =>
        throw new RuntimeException("Bug in type checker. Ill-formed let-expression: " + ex)
    }
  }

  // produce constraints for the binders that are used in a lambda expression
  private def translateBinders(ctx: TypeContext, solver: ConstraintSolver,
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
    val varNames = binders.map(_._1.name).zip(elemVars.map((_, Set[Int]())))
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

  // tired of reading "arguments(s)", it's easy to fix
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
