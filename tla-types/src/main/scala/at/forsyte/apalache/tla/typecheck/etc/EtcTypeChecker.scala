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
        computeRec(rootCtx, rootEx)

      case EtcAppByName(_, _) =>
        computeRec(rootCtx, rootEx)

      // constant expressions need more tests and reporting
      case _ =>
        computeRec(rootCtx, rootEx) match {
          case None =>
            None

          case Some(tt) =>
            if (tt.usedNames.nonEmpty) {
              listener.onTypeError(rootEx.sourceRef, s"Unresolved ${tt.usedNames} in type: $tt")
              None
            } else {
              onTypeFound(rootEx.sourceRef, tt)
              Some(tt)
            }
        }
    }
  }

  private def computeRec(ctx: TypeContext, ex: EtcExpr): Option[TlaType1] = {
    ex match {
      // a type, either monotype or polytype
      case EtcConst(polytype) =>
        Some(polytype) // propagate backwards, some variables may be still not assigned

      // a variable name, either an operator name, or a variable introduced by lambda (STCAbs)
      case EtcName(name) =>
        if (ctx.types.contains(name)) {
          Some(ctx.types(name)) // propagate the type upwards
        } else {
          listener.onTypeError(ex.sourceRef, s"Undefined name $name")
          None
        }

      // the most interesting part: the operator application
      case appEx@EtcApp(operTypes, args@_*) =>
        val pargs = args.map(e => computeRec(ctx, e))

        if (pargs.exists(_.isEmpty)) {
          // there is a problem in the bottom layer, it should have been registered with the listener
          None
        } else {
          // no typing errors so far, do type unification
          val argTypes = pargs.map(_.get) // unpack the option type, now we have a sequence of TlaType1
          matchApp(appEx, operTypes, argTypes)
        }

      // Operator application by name. Resolve the name and pass the resolved expression to the application case.
      case EtcAppByName(name, args@_*) =>
        if (ctx.types.contains(name)) {
          computeRec(ctx, mkApp(ex.sourceRef, Seq(ctx.types(name)), args: _*))
        } else {
          listener.onTypeError(ex.sourceRef, s"Undefined operator name $name")
          None
        }

      // lambda x \in e1, y \in e2, ...: scopedEx
      case EtcAbs(scopedEx, binders@_*) =>
        val names = binders.map(_._1)
        for {
          (_, extCtx) <- matchLambdaDefs(ctx, ex.sourceRef, binders, None)
          // compute the expression in the scope of the extended context
          scopedType <- computeRec(extCtx, scopedEx)
          operType <- Some(OperT1(names.map(extCtx.types), scopedType))
          _ <- Some(onTypeFound(ex.sourceRef, operType))
        } yield operType

      // let name = lambda x \in X, y \in Y, ...: boundEx in scopedEx
      case EtcLet(name, absEx@EtcAbs(boundEx, paramsAndDoms@_*), scopedEx) =>
        val extCtx =
          if (ctx.types.contains(name)) {
            // The definition has a type annotation
            ctx
          } else {
            // Try to compute the type. If it fails, the user has to annotate the definition
            val nargs = paramsAndDoms.length
            val operType = OperT1(1.to(nargs).map(VarT1(_)), VarT1(nargs + 1))
            new TypeContext(ctx.types + (name -> operType))
          }

        for {
          unifiedOperType <- matchDef(extCtx, ex.sourceRef, extCtx(name), paramsAndDoms, boundEx)
          _ <- Some(onTypeFound(absEx.sourceRef, unifiedOperType))
          uniCtx <- Some(new TypeContext(ctx.types + (name -> unifiedOperType)))
          result <- computeRec(uniCtx, scopedEx)
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
    val namedTypeOpts = binders.map { case (name, argEx) => (name, computeRec(ctx, argEx)) }
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
          listener.onTypeError(sourceRef, s"Expected variable $n to be bound by a set, found: $t")
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
          // TODO: rename optParamTypes, so they are distinct from the variables in elemTypes
          val elemTypes = bindingTypes.map(_._2)
          typeUnifier.unify(Substitution.empty, elemTypes.zip(optParamTypes.get)).collect {
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
                       sourceRef: EtcRef,
                       operType: TlaType1,
                       binders: Seq[(String, EtcExpr)],
                       defBody: EtcExpr): Option[TlaType1] = {
    operType match {
      case OperT1(paramTypes, res) =>
        def unifyWithResult(extCtx: TypeContext,
                            inferredResType: TlaType1,
                            expectedResType: TlaType1): Option[TlaType1] = {
          // unify the body type with the operator result, as per the signature
          val unifiedRes = typeUnifier.unify(Substitution.empty, expectedResType, inferredResType)
          if (unifiedRes.isEmpty) {
            listener.onTypeError(sourceRef, s"Expected the result $expectedResType, found $inferredResType")
            None
          } else {
            // All matches, return the unified operator type, which can be used as a result of type inference
            val names = binders.map(_._1)
            val argTypes = names.map(extCtx.types)
            val unifiedResType = unifiedRes.get._2
            onTypeFound(defBody.sourceRef, unifiedResType)
            Some(OperT1(argTypes, unifiedResType))
          }
        }

        for {
          (sub, extCtx) <- matchLambdaDefs(ctx, sourceRef, binders, Some(paramTypes))
          // check the definition body
          inferredResType <- computeRec(extCtx, defBody)
          finalResType <- unifyWithResult(extCtx, inferredResType, sub(res))
        } yield finalResType

      case _ =>
        None
    }
  }

  private def matchApp(appEx: EtcApp,
                       operTypes: Seq[TlaType1],
                       argTypes: Seq[TlaType1]): Option[TlaType1] = {
    // match one operator signature
    def matchOneType: TlaType1 => Option[(Seq[TlaType1], TlaType1)] = {
      case operT@OperT1(paramTypes, resType) =>
        if (paramTypes.length != argTypes.length) {
          listener.onTypeError(appEx.sourceRef,
            "Expected %d arguments, found %d".format(paramTypes.length, argTypes.length))
          None
        } else {
          typeUnifier.unify(Substitution.empty, paramTypes.zip(argTypes)) match {
            case Some((sub, unifiedArgs)) =>
              // Tadaaa. The operator arguments match one of its signatures.
              // However, we have to do plenty of tedious tests.
              // We do not allow type variables escaping the operator application.
              if (unifiedArgs.exists(_.usedNames.nonEmpty)) {
                val usedNames = String.join(", ", unifiedArgs.flatMap(_.usedNames.map(i => VarT1(i).toString)): _*)
                listener.onTypeError(appEx.sourceRef,
                  s"Unresolved $usedNames in operator signature: $operT")
                None
              } else {
                val subResType = sub(resType)
                if (subResType.usedNames.nonEmpty) {
                  val usedNames = String.join(", ", subResType.usedNames.toSeq.map(i => VarT1(i).toString): _*)
                  listener.onTypeError(appEx.sourceRef,
                    s"Unresolved $usedNames in operator signature: $operT")
                  None
                } else {
                  Some((unifiedArgs, subResType))
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
      val separated = String.join(", ", argTypes.map(_.toString): _*)
      listener.onTypeError(appEx.sourceRef, "No matching signature for argument type(s): " + separated)
      None
    } else if (matches.length > 1) {
      val separated = String.join(", ", argTypes.map(_.toString): _*)
      listener.onTypeError(appEx.sourceRef,
        s"${matches.length} matching signatures for argument type(s): $separated")
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

  private def onTypeFound(sourceRef: EtcRef, tt: TlaType1): Unit = {
    sourceRef match {
      case ref: ExactRef =>
        listener.onTypeFound(ref, tt)

      case _ =>
    }
  }
}
