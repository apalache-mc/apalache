package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecomp.TBuilderTypeException
import at.forsyte.apalache.tla.types.{Substitution, TypeUnifier, TypeVarPool}

/**
 * Scope-unsafe builder for base TlaOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeBaseBuilder extends ProtoBuilder with UnsafeLiteralAndNameBuilder {
  // We extend the LiteralBuilder to make TLA strings from Scala strings

  /** {{{lhs = rhs}}} */
  def eql(lhs: TlaEx, rhs: TlaEx): TlaEx = buildBySignatureLookup(TlaOper.eq, lhs, rhs)

  /** {{{lhs /= rhs}}} */
  def neql(lhs: TlaEx, rhs: TlaEx): TlaEx = buildBySignatureLookup(TlaOper.ne, lhs, rhs)

  /** {{{Op(args[1],...,args[n])}}} */
  def appOp(Op: TlaEx, args: TlaEx*): TlaEx = {
    // To support polymorphic operators, we first attempt to compute the post-unification types
    val opType = TlaType1.fromTypeTag(Op.typeTag)
    require(opType.isInstanceOf[OperT1], s"appOp of ${Op} not tagged with type OperT1, but ${opType}")
    val OperT1(_, resT) = opType.asInstanceOf[OperT1]
    val argTs = args.map(a => TlaType1.fromTypeTag(a.typeTag))
    val mockOperT = OperT1(argTs, resT)
    val unifOpt = new TypeUnifier(new TypeVarPool()).unify(Substitution.empty, opType, mockOperT)

    unifOpt match {
      case Some((subst, unifiedOperT)) =>
        val retypedArgs = args.zip(argTs).map { case (arg, argT) =>
          arg.withTag(Typed(subst.subRec(argT)))
        }
        val retypedOp = Op.withTag(Typed(unifiedOperT))

        retypedOp match {
          // This is a workaround for the fact that that we currently de-lambda,
          // because lambdas are not supported in the Apalache IR. See
          // https://github.com/apalache-mc/apalache/issues/2532
          case LetInEx(nameEx @ NameEx(operName), decl) if operName == decl.name =>
            val appliedByName = buildBySignatureLookup(TlaOper.apply, nameEx +: retypedArgs: _*)
            LetInEx(appliedByName, decl)(appliedByName.typeTag)
          case _ => buildBySignatureLookup(TlaOper.apply, retypedOp +: retypedArgs: _*)
        }
      case None =>
        throw new TBuilderTypeException(
            s"Operator application argument types ${mockOperT} do not unify with the operator type ${opType} in ${Op}(${args
                .mkString(", ")}).")
    }

  }

  /**
   * {{{CHOOSE x: p}}}
   * @param x
   *   must be a variable name
   */
  def choose(x: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx], s"Expected x to be a variable name, found $x.")
    buildBySignatureLookup(TlaOper.chooseUnbounded, x, p)
  }

  /**
   * {{{CHOOSE x \in set: p}}}
   * @param x
   *   must be a variable name
   */
  def choose(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx], s"Expected x to be a variable name, found $x.")
    buildBySignatureLookup(TlaOper.chooseBounded, x, set, p)
  }

  /**
   * {{{args[0](args[1], ..., args[n]) :: ex}}}
   * @param args
   *   must be nonempty
   */
  def label(ex: TlaEx, args: String*): TlaEx = {
    require(args.nonEmpty, s"args must be nonempty.")
    val argsAsStringExs = args.map { str }
    buildBySignatureLookup(TlaOper.label, ex +: argsAsStringExs: _*)
  }
}
