package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck._

import scala.collection.immutable.SortedMap

/**
  * ETC: Embarrassingly simple Type Checker.
  *
  * @author Igor Konnov
  */
class EtcTypeChecker extends TypeChecker with EtcBuilder {
  private val typeUnifier: TypeUnifier = new TypeUnifier()
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
    rootEx match {
      // operator applications do all checks and reporting by themselves
      case EtcApp(_, _) =>
        computeRec(rootCtx, rootEx, None)

      case EtcAppByName(_, _) =>
        computeRec(rootCtx, rootEx, None)

      // constant expressions need more tests and reporting
      case _ =>
        computeRec(rootCtx, rootEx, None) match {
          case None =>
            None

          case Some(tt) =>
            if (tt.usedNames.nonEmpty) {
              onTypeError(rootEx.sourceRef, s"Unresolved ${tt.usedNames} in type: $tt")
              None
            } else {
              onTypeFound(rootEx.sourceRef, tt)
              Some(tt)
            }
        }
    }
  }

  private def computeRec(ctx: TypeContext, ex: EtcExpr, forcedResult: Option[TlaType1]): Option[TlaType1] = {
    ex match {
      // a type: either monotype or polytype
      case EtcConst(polytype) =>
        if (forcedResult.isEmpty) {
          Some(polytype) // propagate backwards, some variables may be still not assigned
        } else {
          // unify the polytype with the forced result (propagated from an annotation).
          // Complain if they cannot be unified.
          typeUnifier.unify(Substitution.empty, polytype, forcedResult.get) match {
            case None =>
              onTypeError(ex.sourceRef, s"Expected %s from annotation, found %s".format(forcedResult.get, polytype))
              None

            case Some((_, refined)) =>
              Some(refined)
          }
        }

      // an inline type declaration
      case EtcTypeDecl(name: String, declaredType: TlaType1, scopedEx: EtcExpr) =>
        val extCtx = new TypeContext(ctx.types + (name -> declaredType))
        // propagate the forced result downwards
        computeRec(extCtx, scopedEx, forcedResult)

      // a variable name, either an operator name, or a variable introduced by lambda (STCAbs)
      case EtcName(name) =>
        if (ctx.types.contains(name)) {
          // process as a constant, as we might want to force the expected result
          computeRec(ctx, mkConst(BlameRef(ex.sourceRef.tlaId), ctx.types(name)), forcedResult)
        } else {
          onTypeError(ex.sourceRef, s"Undefined name $name. Introduce a type annotation.")
          None
        }

      // the most interesting part: the operator application
      case appEx@EtcApp(operTypes, args@_*) =>
        val pargs = args.map(e => computeRec(ctx, e, None)) // the parameter types are not enforced

        if (pargs.exists(_.isEmpty)) {
          // there is a problem in the bottom layer, it should have been registered with the listener
          None
        } else {
          // no typing errors so far, do type unification
          val argTypes = pargs.map(_.get) // unpack the option type, now we have a sequence of TlaType1
          matchApp(appEx, operTypes, argTypes, forcedResult)
        }

      // Operator application by name. Resolve the name and pass the resolved expression to the application case.
      case EtcAppByName(name, args@_*) =>
        if (ctx.types.contains(name)) {
          computeRec(ctx, mkApp(ex.sourceRef, Seq(ctx.types(name)), args: _*), forcedResult)
        } else {
          onTypeError(ex.sourceRef, s"Undefined operator name $name. Introduce a type annotation.")
          None
        }

      // lambda x \in e1, y \in e2, ...: scopedEx
      case EtcAbs(scopedEx, binders@_*) =>
        val names = binders.map(_._1)
        for {
          (_, extCtx) <- matchLambdaDefs(ctx, ex.sourceRef, binders, None)
          // compute the expression in the scope of the extended context
          scopedType <- computeRec(extCtx, scopedEx, forcedResult)
          operType <- Some(OperT1(names.map(extCtx.types), scopedType))
          _ <- Some(onTypeFound(ex.sourceRef, operType))
        } yield operType

      // let name = lambda x \in X, y \in Y, ...: boundEx in scopedEx
      case EtcLet(name, absEx@EtcAbs(boundEx, paramsAndDoms@_*), scopedEx) =>
        val extCtx =
          ctx.types.get(name) match {
            case Some(OperT1(_, _)) =>
              // the definition has a type annotation
              ctx

            case Some(someType: TlaType1) =>
              // The definition has a type annotation which is not an operator. Assume it is a nullary operator.
              // Strictly speaking, this is a hack. However, it is quite common to declare a constant with LET.
              new TypeContext(ctx.types + (name -> OperT1(Seq(), someType)))

            case None =>
              // Try to compute the type. If it fails, the user has to annotate the definition
              val nargs = paramsAndDoms.length
              val operType = OperT1(1.to(nargs).map(VarT1(_)), VarT1(nargs + 1))
              new TypeContext(ctx.types + (name -> operType))
          }

        for {
          // unify the parameter types in the signature and the types of the actual parameters
          unifiedOperType <- matchDef(extCtx, name, ex.sourceRef, paramsAndDoms, boundEx)
          _ <- Some(onTypeFound(absEx.sourceRef, unifiedOperType))
          uniCtx <- Some(new TypeContext(ctx.types + (name -> unifiedOperType)))
          // compute the expression in the scope by assuming the instantiated signature
          result <- computeRec(uniCtx, scopedEx, forcedResult)
          _ <- Some(onTypeFound(ex.sourceRef, result))
        } yield result

      // an ill-formed let expression
      case EtcLet(_, _, _) =>
        throw new RuntimeException("Bug in type checker. Ill-formed let-expression: " + ex)
    }
  }

  // Process the lambda definitions, but not the expression under the lambda definition.
  // Optionally, the types of the variables may be constrained with optParamTypes.
  //
  // lambda x \in e1, y \in e2, ...: scopedEx
  private def matchLambdaDefs(ctx: TypeContext,
                              sourceRef: EtcRef,
                              binders: Seq[(String, EtcExpr)],
                              optParamTypes: Option[Seq[TlaType1]]): Option[(Substitution, TypeContext)] = {
    // check, whether the domain types are well-typed
    val namedTypeOpts = binders.map { case (name, argEx) => (name, computeRec(ctx, argEx, None)) }
    if (namedTypeOpts.exists(_._2.isEmpty)) {
      // type checking has failed for a binding set, this is reported in the bottom layer
      None
    } else {
      // check that the variable domains are typed to sets
      val bindingTypes = namedTypeOpts.collect { case (name, Some(SetT1(elemType))) => (name, elemType) }
      if (bindingTypes.length < binders.length) {
        // some binding expressions are resolved to non-sets, report
        val failedNames = Set(binders.map(_._1): _*) -- Set(bindingTypes.map(_._1): _*)
        val failedNamesAndSets =
          namedTypeOpts.collect { case (name, Some(tt)) if failedNames.contains(name) => (name, tt) }
        for ((n, t) <- failedNamesAndSets) {
          onTypeError(sourceRef, s"Expected variable $n to be bound by a set, found: $t")
        }
        None
      } else {
        if (optParamTypes.isEmpty) {
          // return an empty substitution and the context extended with variable bindings
          val extCtx = new TypeContext(ctx.types ++ SortedMap(bindingTypes: _*))
          // register the types of the binding sets
          for ((setEx, elemType) <- binders.map(_._2).zip(bindingTypes.map(_._2))) {
            onTypeFound(setEx.sourceRef, SetT1(elemType))
          }
          Some((Substitution.empty, extCtx))
        } else {
          // unify optParamTypes with element types
          val elemTypes = bindingTypes.map(_._2)
          val uniqueSub = uniqueSubstitution(optParamTypes.get, elemTypes)
          val uniqueElemTypes = elemTypes.map(uniqueSub(_))

          typeUnifier.unify(Substitution.empty, uniqueElemTypes.zip(optParamTypes.get)).collect {
            case (sub, unifiedArgs) =>
              // all good, extend the context with the bindings for the lambda variables
              val bindings = bindingTypes.map(_._1).zip(unifiedArgs)
              // register the types of the binding sets
              for ((setEx, elemType) <- binders.map(_._2).zip(bindings.map(_._2))) {
                onTypeFound(setEx.sourceRef, SetT1(elemType))
              }
              // extend the context
              val extCtx = new TypeContext(ctx.types ++ SortedMap(bindings: _*))
              (sub, extCtx)
          }
        }
      }
    }
  }

  private def matchDef(ctx: TypeContext,
                       name: String,
                       sourceRef: EtcRef,
                       binders: Seq[(String, EtcExpr)],
                       defBody: EtcExpr): Option[TlaType1] = {
    ctx(name) match {
      case OperT1(paramTypes, res) =>
        def unifyWithResult(extCtx: TypeContext,
                            inferredResType: TlaType1,
                            expectedResType: TlaType1): Option[TlaType1] = {
          // unify the body type with the operator result, as per the signature
          val unifiedRes = typeUnifier.unify(Substitution.empty, expectedResType, inferredResType)
          if (unifiedRes.isEmpty) {
            onTypeError(sourceRef, s"Expected the result $expectedResType, found $inferredResType")
            None
          } else {
            // All matches, return the unified operator type, which can be used as a result of type inference
            val names = binders.map(_._1)
            val argTypes = names.map(extCtx.types)
            val unifiedResType = unifiedRes.get._2
            // We check on purpose that neither the unified arguments, nor the results are polymorphic.
            // In the future, we might want to lift this restriction, but polymorphism tends to delay type errors.
            val inferredOperType = OperT1(argTypes, unifiedResType)
            if (argTypes.exists(_.usedNames.nonEmpty) || unifiedResType.usedNames.nonEmpty) {
              onTypeError(sourceRef,
                s"Expected a concrete type of operator $name, found polymorphic type: " + inferredOperType)
              None
            } else {
              onTypeFound(defBody.sourceRef, unifiedResType)
              Some(inferredOperType)
            }
          }
        }

        // We only enforce the result for nullary operators (i.e., constants), to resolve overloading.
        // Otherwise, we would break contra-variance and thus break (Reynolds'?) substitution principle.
        val forcedResult = if (paramTypes.isEmpty) Some(res) else None

        for {
          (sub, extCtx) <- matchLambdaDefs(ctx, sourceRef, binders, Some(paramTypes))
          // check the definition body
          inferredResType <- computeRec(extCtx, defBody, forcedResult)
          finalResType <- unifyWithResult(extCtx, inferredResType, sub(res))
        } yield finalResType

      case _ =>
        None
    }
  }

  private def matchApp(appEx: EtcApp,
                       operTypes: Seq[TlaType1],
                       argTypes: Seq[TlaType1],
                       forcedResult: Option[TlaType1]): Option[TlaType1] = {
    // match one operator signature
    def matchOneType: TlaType1 => Option[(Seq[TlaType1], TlaType1)] = {
      case operT@OperT1(paramTypes, resType) =>
        if (paramTypes.length != argTypes.length) {
          onTypeError(appEx.sourceRef, "Expected %d arguments, found %d".format(paramTypes.length, argTypes.length))
          None
        } else {
          // Make sure that the operator signatures does not clash with the arguments on the free variables.
          // To this end, we may rename the free variables in the operator signature.
          val paramSub = uniqueSubstitution(argTypes, resType +: paramTypes)
          val renResType = paramSub(resType)
          val renParamTypes = paramTypes.map(paramSub(_))
          val renOperT = paramSub(operT)
          // freeVars are the free variables in the signature, which must be resolved.
          // Note that argTypes also may have free variables; they may stay unresolved at this level
          val freeVars = renParamTypes.foldLeft(renResType.usedNames) { (s, t) => s ++ t.usedNames}

          typeUnifier.unify(Substitution.empty, renParamTypes.zip(argTypes)) match {
            case Some((sub, unifiedArgs)) =>
              def unresolved(t: TlaType1) = t.usedNames.intersect(freeVars).map(i => VarT1(i).toString)

              // Tadaaa. The operator arguments match one of its signatures.
              // However, we have to do plenty of tedious tests.
              // We do not allow type variables escaping the operator application.
              if (unifiedArgs.exists(_.usedNames.intersect(freeVars).nonEmpty)) {
                val usedNames = String.join(", ", unifiedArgs.flatMap(unresolved): _*)
                onTypeError(appEx.sourceRef, s"Unresolved $usedNames in operator signature: $renOperT")
                None
              } else {
                val subResType = sub(renResType)
                if (subResType.usedNames.intersect(freeVars).nonEmpty) {
                  val usedNames = String.join(", ", unresolved(subResType).toSeq: _*)
                  onTypeError(appEx.sourceRef, s"Unresolved $usedNames in operator signature: $renOperT")
                  None
                } else {
                  // Everything is computed. If the result should be forced, see if it allows us to reject the signature.
                  if (forcedResult.isEmpty) {
                    Some((unifiedArgs, subResType))
                  } else {
                    // both types may clash on type variable, rename subResType
                    val forceSub = uniqueSubstitution(Seq(forcedResult.get), Seq(subResType))
                    // if the types can be unified, return the resulting signature
                    typeUnifier.unify(Substitution.empty, forcedResult.get, forceSub(subResType))
                      .map { case (_, result) => (unifiedArgs, result) }
                  }
                }
              }

            case None => None
          }
        }

      case tt@_ =>
        throw new RuntimeException("Bug in type checker. Expected OperT1, found: " + tt)
    }

    val matches = operTypes.map(matchOneType).collect { case Some(p) => p }

    if (matches.isEmpty) {
      val separated = String.join(" and ", argTypes.map(_.toString): _*)
      onTypeError(appEx.sourceRef, "No matching signature for argument type(s): " + separated)
      None
    } else if (matches.length > 1) {
      val separatedArgs = String.join(" and ", argTypes.map(_.toString): _*)
      val separatedSigs = String.join(" and ", matches.map(p => OperT1(p._1, p._2).toString()) :_*)
      onTypeError(appEx.sourceRef,
        s"Need annotation. Argument type(s) $separatedArgs produce ${matches.length} signatures: " + separatedSigs)
      None
    } else {
      // all good
      val (unifiedArgs, unifiedRes) = matches.head
      // All names have been resolved. We can report on the types of the operator and its arguments.
      // As we are reporting the argument types, the listener may receive type information multiple times.
      appEx.args.zip(unifiedArgs).foreach { case (arg, argT) => onTypeFound(arg.sourceRef, argT) }
      onTypeFound(appEx.sourceRef, unifiedRes)

      Some(unifiedRes)
    }
  }

  // if primary and secondary intersect on the sets of used variables, produce a substitution that renames secondary
  private def uniqueSubstitution(primary: Seq[TlaType1], secondary: Seq[TlaType1]): Substitution = {
    val pInt = TlaType1.joinVarIntervals(primary :_*)
    val sInt = TlaType1.joinVarIntervals(secondary :_*)
    if (pInt._2 > sInt._1 || sInt._2 > pInt._1) {
      val usedVars = secondary.foldLeft(Set[Int]()) { case (s, t) => s ++ t.usedNames }
      // shift the variable indices
      val shift = usedVars.toSeq.map(i => i -> VarT1(i + pInt._2))
      Substitution(shift :_*)
    } else {
      // no intersection
      Substitution()
    }
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
