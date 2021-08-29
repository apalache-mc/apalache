package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.io.annotations.store.createAnnotationStore
import at.forsyte.apalache.tla.lir
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.typecheck.etc._

object TypeInfer {
  // a static empty annotation store that we pass to ToEtcExpr
  private val emptyAnnotationStore = createAnnotationStore()

  /**
   * Adapter of a builder expression into a TlaEx that infers types, whenever possible.
   * This class is marked as 'implicit', so we can apply `inferType` to a builder expression.
   *
   * @param bex a builder expression.
   * @author Igor Konnov (version 2), Jure Kukovec (version 1)
   */
  implicit class BuilderExInfer(bex: BuilderEx) {

    /**
     * Infer the type of the expression under construction.
     * This method is semi-automatic. It assumes that all names are supplied with
     * types by using the method BuilderDeclAsTyped.as, e.g., `name("x") as IntT1()`.
     * This method is mainly intended to be used in unit tests to increase the readability
     * of constructed expressions. Use direct type annotations by applying the method `as`.
     * Do not use this method in the non-test code, as it may fail in unusual cases,
     * e.g., when an empty set is passed.
     *
     * @return the constructed expression that is tagged with the type that was inferred.
     * @throws BuilderError on a malformed expression or type error
     */
    def inferType(): TlaEx = {
      bex match {
        case BuilderTlaExWrapper(ex) =>
          ex

        // there are a few edge cases that require special handling
        case BuilderOper(TlaSetOper.enumSet) =>
          throw new BuilderError("Empty set needs a type, use: enumSet() as typ")

        case BuilderOper(TlaFunOper.tuple) =>
          throw new BuilderError("Empty tuple/sequence needs a type, use: tuple() as typ")

        // the general case
        case BuilderOper(oper, args @ _*) =>
          // infer the argument types
          val inferredArgs = args map (a => BuilderExInfer(a).inferType())
          val varPool = new TypeVarPool()
          val toEtc = new ToEtcExpr(emptyAnnotationStore, ConstSubstitution.empty, varPool)
          // 1. Introduce a fresh name for every argument
          // To avoid collisions with other names, use the cryptic prefix '?_'.
          val argNames = 1.to(inferredArgs.size).map(i => s"?_$i")
          val replacedArgs = argNames.zip(inferredArgs).map {
            case (_, v @ ValEx(_)) =>
              // keep the value, as some operators expect ValEx(TlaStr(_))
              v

            case (_, OperEx(TlaFunOper.tuple, _*)) if oper == TlaFunOper.except =>
              // weird corner case in EXCEPT: the accessors are always wrapped with a tuple
              throw new BuilderError("EXCEPT requires accessors to be wrapped in a tuple. Use a manual annotation.")

            case (n, _) =>
              // use an untyped name, which is bound to the type from `inferredArgs` in bindings (below)
              NameEx(n)(Untyped())
          }
          // 2. Construct the untyped expression over the operator and names.
          val etcExpr = toEtc(OperEx(oper, replacedArgs: _*)(Untyped()))
          // 3. Produce a small set of constraints and solve them
          val bindings = argNames.zip(inferredArgs).map { case (n, a) => n -> a.typeTag.asTlaType1() }
          val inferCtx = new InferContext(new ConstraintSolver(), varPool, Map(bindings: _*))
          try {
            val resultVar = mkConstraints(inferCtx, etcExpr)

            inferCtx.solver.solve() match {
              case None =>
                val args_s = inferredArgs.map(_.toString).mkString(", ")
                throw new BuilderError(s"Type inference error for operator ${oper.name} applied to: $args_s")

              case Some(sub) =>
                val inferredType = sub.subRec(resultVar)
                OperEx(oper, inferredArgs: _*)(Typed(inferredType))
            }
          } catch {
            case e: BuilderError =>
              throw new BuilderError(s"inferType for ${oper.name} failed: " + e.getMessage)
          }

        case BuilderName(name) =>
          throw new BuilderError(s"Instead of inferType(), use: $name as tt")

        case BuilderAlias(_, alias) =>
          throw new BuilderError(s"Instead of ex ? $alias, use: ex as tt")

        case BuilderLet(body, defs @ _*) =>
          val builtBody = BuilderExInfer(body).inferType()
          LetInEx(builtBody, defs: _*)(builtBody.typeTag)

        case BuilderVal(TlaInt(value)) =>
          ValEx(TlaInt(value))(Typed(IntT1()))

        case BuilderVal(TlaBool(value)) =>
          ValEx(TlaBool(value))(Typed(BoolT1()))

        case BuilderVal(TlaStr(value)) =>
          ValEx(TlaStr(value))(Typed(StrT1()))

        case BuilderVal(TlaIntSet) =>
          ValEx(TlaIntSet)(Typed(SetT1(IntT1())))

        case BuilderVal(TlaNatSet) =>
          ValEx(TlaNatSet)(Typed(SetT1(IntT1())))

        case BuilderVal(TlaBoolSet) =>
          ValEx(TlaBoolSet)(Typed(SetT1(BoolT1())))

        case BuilderVal(TlaRealSet) =>
          ValEx(TlaRealSet)(Typed(SetT1(RealT1())))

        case BuilderVal(v) =>
          throw new BuilderError("Unexpected value: " + v)
      }
    }

    // This is a simplified version of EtcTypeChecker.compute that is tuned for the method infer().
    // Most importantly, this method is intended for the internal use. Hence, every type error is an indicator
    // of an internal error in the code. We do not have to produce very detailed error messages.
    private def mkConstraints(ctx: InferContext, etcEx: EtcExpr): TlaType1 = {
      etcEx match {
        case EtcConst(tt) =>
          // a type constant, just return it
          tt

        case EtcApp(operTypes, args @ _*) =>
          // Introduce constraints for application by type.
          // operVar = (arg_1, ..., arg_k) => resVar
          val argTypes = args.toList.map(arg => mkConstraints(ctx, arg))
          val resVar = ctx.varPool.fresh
          val operVar = ctx.varPool.fresh
          val operSig = lir.OperT1(argTypes, resVar)

          def onTypeError(sub: Substitution, types: Seq[TlaType1]): Unit = {
            // no solution for: operVar = (arg_1, ..., arg_k) => resVar
            val evalArgTypes = argTypes.map(sub.subRec).mkString(", ")
            throw new BuilderError(s"Operator type $operSig and argument(s) $evalArgTypes")
          }

          ctx.solver.addConstraint(EqClause(operVar, operSig)
                .setOnTypeError(onTypeError))

          if (operTypes.length == 1) {
            // the common case, which should be solved without using OrClause (which can be postponed):
            // operVar = operType_1
            ctx.solver.addConstraint(EqClause(operVar, operTypes.head).setOnTypeError(onTypeError))
          } else {
            // the case of overloaded operators:
            // operVar = operType_1 \/ ... \/ operVar = operType_n
            ctx.solver.addConstraint(OrClause(operTypes.map(EqClause(operVar, _)): _*)
                  .setOnTypeError(onTypeError)
                  .asInstanceOf[OrClause])
          }

          // the expected result is stored in resVar
          resVar

        case EtcName(name) =>
          ctx.bindings.get(name) match {
            case Some(tt) =>
              tt

            case None =>
              throw new BuilderError(s"Name $name is not in the context")
          }

        case EtcAppByName(nameEx, args @ _*) =>
          ctx.bindings.get(nameEx.name) match {
            case None =>
              throw new BuilderError(s"Operator name ${nameEx.name} is not in the context")

            case Some(tt) =>
              mkConstraints(ctx, EtcApp(Seq(tt), args: _*)(etcEx.sourceRef))
          }

        case _ =>
          throw new BuilderError(s"Unexpected expression $etcEx")
      }
    }

    private class InferContext(val solver: ConstraintSolver, val varPool: TypeVarPool,
        val bindings: Map[String, TlaType1]) {}
  }
}
