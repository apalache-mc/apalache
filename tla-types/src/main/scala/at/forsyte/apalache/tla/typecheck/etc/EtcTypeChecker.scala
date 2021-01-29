package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.etc.EtcTypeChecker.UnwindException

/**
  * ETC: Embarrassingly simple Type Checker.
  *
  * @author Igor Konnov
  */
class EtcTypeChecker(varPool: TypeVarPool) extends TypeChecker with EtcBuilder {
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
          val exactType = sub(rootType)
          if (exactType.usedNames.nonEmpty) {
            onTypeError(rootEx.sourceRef,
              s"Expected the top expression to have a concrete type, found polymorphic type: " + exactType)
            None
          } else {
            onTypeFound(rootEx.sourceRef, exactType)
            Some(exactType)
          }
      }

    } catch {
      case _: UnwindException =>
        // the type checker has flagged a type error down in the syntax tree
        None
    }
  }

  private def computeRec(ctx: TypeContext, solver: ConstraintSolver, ex: EtcExpr): TlaType1 = {
    ex match {
      // a type: either monotype or polytype
      case EtcConst(polytype) =>
        // add the constraint: x = polytype, for a fresh x
        val fresh = varPool.fresh
        val clause = EqClause(fresh, polytype)
            .setOnTypeFound(onTypeFound(ex.sourceRef, _))
            .setOnTypeError(_ => onTypeError(ex.sourceRef, "Unresolved type"))
        solver.addConstraint(clause)
        fresh

      // an inline type declaration
      case EtcTypeDecl(name: String, declaredType: TlaType1, scopedEx: EtcExpr) =>
        // Just propagate the annotated name down the tree. It will be used in a let definition.
        val extCtx = new TypeContext(ctx.types + (name -> declaredType))
        computeRec(extCtx, solver, scopedEx)

      // a variable name, either an operator name, or a variable introduced by lambda (EtcAbs)
      case EtcName(name) =>
        if (ctx.types.contains(name)) {
          // process as a constant, as we might want to force the expected result
          computeRec(ctx, solver, mkConst(ex.sourceRef, ctx.types(name)))
        } else {
          onTypeError(ex.sourceRef, s"Undefined name $name. Introduce a type annotation.")
          throw new UnwindException
        }

      // the most interesting part: the operator application
      case appEx@EtcApp(operTypes, args@_*) =>
        val argTypes = args.map(arg => computeRec(ctx, solver, arg))
        val resVar = varPool.fresh
        val operVar = varPool.fresh

        def onFound: TlaType1 => Unit = {
          case OperT1(_, res) =>
            // report the result of operator application, not the operator type itself
            onTypeFound(ex.sourceRef, res)

          case tt =>
            throw new TypingException("Expected an operator type, found: " + tt)
        }
        def onError(types: Seq[TlaType1]): Unit = {
          val sepSigs = String.join(" and ", types.map(_.toString()) :_*)
          if (types.isEmpty) {
            onTypeError(appEx.sourceRef, s"No matching signature for ${argTypes.length} argument(s)")
          } else if (types.length > 1) {
            onTypeError(appEx.sourceRef,
              s"Need annotation. Arguments match ${types.length} operator signatures: $sepSigs")
          } else {
            onTypeError(appEx.sourceRef, s"Mismatch in argument types. Expected: $sepSigs")
          }
        }

        // operVar = (arg_1, ..., arg_k) => resVar
        solver.addConstraint(EqClause(operVar, OperT1(argTypes, resVar))
          .setOnTypeFound(onFound)
          .setOnTypeError(onError))
        // operVar = operType_1 \/ ... \/ operVar = operType_n
        solver.addConstraint(OrClause(operTypes.map(EqClause(operVar, _)) :_*)
          .setOnTypeError(onError).asInstanceOf[OrClause])

          // the expected result is stored in resVar
        resVar

      // Operator application by name. Resolve the name and pass the resolved expression to the application case.
      case EtcAppByName(name, args@_*) =>
        if (ctx.types.contains(name)) {
          computeRec(ctx, solver, mkApp(ex.sourceRef, Seq(ctx.types(name)), args: _*))
        } else {
          onTypeError(ex.sourceRef, s"Undefined operator name $name. Introduce a type annotation.")
          throw new UnwindException
        }

      // lambda x \in e1, y \in e2, ...: scopedEx
      case EtcAbs(scopedEx, binders@_*) =>
        val extCtx = translateBinders(ctx, solver, binders)
        // compute the expression in the scope
        val underlyingType = computeRec(extCtx, solver, scopedEx)
        // introduce a variable for lambda, in order to propagate the type to the listener
        val lambdaTypeVar = varPool.fresh
        val varNames = binders.map { case (name, _) => extCtx(name) }
        val operType = OperT1(varNames, underlyingType)
        // lambdaTypeVar = (a_1, ..., a_k) => resType
        val lambdaClause = EqClause(lambdaTypeVar, operType)
            .setOnTypeFound(tt => onTypeFound(ex.sourceRef, tt))
            .setOnTypeError(ts => onTypeError(ex.sourceRef.asInstanceOf[ExactRef],
              "Type error in lambda: " + ts.head))
        solver.addConstraint(lambdaClause)
        operType

      // let name = lambda x \in X, y \in Y, ...: boundEx in scopedEx
      case EtcLet(name, defEx@EtcAbs(defBody, binders@_*), scopedEx) =>
        // Before analyzing the operator definition, try to partially solve the equations in the current context.
        // If it is successful, use the partial solution to refine the types in the type context.
        val approxSolution = solver.solvePartially().getOrElse(throw new UnwindException)

        // introduce a new instance of the constraint solver for the operator definition
        val letInSolver = new ConstraintSolver()
        val operSig =
          ctx.types.get(name) match {
          case Some(declaredType @ OperT1(_, _)) =>
            declaredType

          case Some(someType: TlaType1) =>
            // The definition has a type annotation which is not an operator. Assume it is a nullary operator.
            // Strictly speaking, this is a hack. However, it is quite common to declare a constant with LET.
            OperT1(Seq(), someType)

          case None =>
            // Let the solver compute the type. If it fails, the user has to annotate the definition
            OperT1(1.to(binders.length).map(_ => varPool.fresh), varPool.fresh)
        }

        // translate the binders in the lambda expression, so we can quickly propagate the types of the parameters
        val preCtx = new TypeContext((ctx.types + (name -> operSig)).mapValues(approxSolution(_)))
        val extCtx = translateBinders(preCtx, letInSolver, binders)
        val annotationParams = operSig.asInstanceOf[OperT1].args
        annotationParams.zip(binders.map { case (pname, _) => (pname, extCtx(pname)) }).foreach {
          case (annotParam, (pname, paramVar @ VarT1(_))) =>
            val clause = EqClause(paramVar, annotParam)
              .setOnTypeError(ts => s"Mismatch in parameter $pname. Found: " + ts.head)
            letInSolver.addConstraint(clause)
        }

        // produce constraints for the operator signature
        def onError(ts: Seq[TlaType1]): Unit = {
          val sepSigs = String.join(" and ", ts.map(_.toString()) :_*)
          onTypeError(defEx.sourceRef, s"Expected $operSig in $name. Found: $sepSigs")
        }

        val operVar = varPool.fresh
        val sigClause = EqClause(operVar, operSig)
          .setOnTypeFound(onTypeFound(defEx.sourceRef, _))
          .setOnTypeError(onError)
        letInSolver.addConstraint(sigClause)

        // compute the constraints for the operator definition
        val defBodyType = computeRec(extCtx, letInSolver, defBody)
        val paramTypes = binders.map(p => extCtx(p._1))
        val defType = OperT1(paramTypes, defBodyType)
        // add the constraint from the annotation
        val defClause = EqClause(operVar, defType)
            .setOnTypeFound(onTypeFound(defEx.sourceRef, _))
            .setOnTypeError(onError)

        letInSolver.addConstraint(defClause)

        val preciseDefType =
          letInSolver.solve() match {
            case None =>
              onTypeError(ex.sourceRef, s"Error when computing the type of $name")
              throw new UnwindException

            case Some(sub) =>
              sub(defType)
          }

        if (preciseDefType.usedNames.nonEmpty) {
          onTypeError(ex.sourceRef,
            s"Expected a concrete type of operator $name, found polymorphic type: " + preciseDefType)
          throw new UnwindException
        }

        // TODO: check that the inferred signature matches the annotation?

        // compute the type of the expression under the definition
        val underCtx = new TypeContext(ctx.types + (name -> preciseDefType))
        computeRec(underCtx, solver, scopedEx)

      // an ill-formed let expression
      case EtcLet(_, _, _) =>
        throw new RuntimeException("Bug in type checker. Ill-formed let-expression: " + ex)
    }
  }

  // produce constraints for the binders that are used in a lambda expression
  private def translateBinders(ctx: TypeContext,
                               solver: ConstraintSolver,
                               binders: Seq[(String, EtcExpr)]): TypeContext = {
    val setTypes = binders.map(binder => computeRec(ctx, solver, binder._2))
    // introduce type variables b_1, ..., b_k for the binding sets
    val setVars = 1.to(binders.size).map(_ => varPool.fresh)
    // ...and type variables a_1, ..., a_k for the set elements
    val elemVars = 1.to(binders.size).map(_ => varPool.fresh)
    // require that these type variables capture the sets: b_i = Set(a_i) for 1 <= i <= k
    binders.zip(setVars.zip(elemVars)).foreach { case ((_, setEx), (setVar, elemVar)) =>
      val clause = EqClause(setVar, SetT1(elemVar))
        .setOnTypeFound(onTypeFound(setEx.sourceRef, _))
        .setOnTypeError(ts => onTypeError(setEx.sourceRef, "Expected a set. Found: " + ts.head))
      solver.addConstraint(clause)
    }
    // require that these type variables are equal to the computed set types
    binders.zip(setVars.zip(setTypes)).foreach { case ((_, setEx), (setVar, setType)) =>
      val clause = EqClause(setVar, setType)
        .setOnTypeError(ts => onTypeError(setEx.sourceRef, "Expected a set. Found: " + ts.head))
      solver.addConstraint(clause)
    }
    // compute the expression in the scope, by associating the variables names with the elements of elemVars
    new TypeContext(ctx.types ++ binders.map(_._1).zip(elemVars))
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
}

object EtcTypeChecker {

  /**
    * We use this exception to quickly unwind the search stack
    */
  protected class UnwindException extends RuntimeException
}
