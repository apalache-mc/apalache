package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.oper.{OperArity, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, TlaType1, Typed}
import scalaz._
import scalaz.Scalaz._

/**
 * Utility methods
 *
 * @author
 *   Jure Kukovec
 */
object BuilderUtil {

  /**
   * Constructs an OperEx expression for oper applied to args. Uses typeCmp to validate args and determine the result
   * type
   */
  def composeAndValidateTypes(oper: TlaOper, typeCmp: TypeComputation, args: TlaEx*): TlaEx = typeCmp(args) match {
    case Left(err) => throw err
    case Right(typeRes) =>
      OperEx(oper, args: _*)(Typed(typeRes))
  }

  /**
   * Returns the variable or set of variables, if elem is either a variable name or a tuple of variable names, otherwise
   * throws an IllegalArgumentException.
   */
  def getBoundVarsOrThrow(elem: TlaEx): Set[String] = elem match {
    case NameEx(name) => Set(name)
    case OperEx(TlaFunOper.tuple, args @ _*) if args.forall(_.isInstanceOf[NameEx]) =>
      val varnames = args.map { _.asInstanceOf[NameEx].name }.toSet
      if (varnames.size < args.size)
        throw new IllegalArgumentException(
            s"requirement failed: Expected elem to be a tuple of unique variable names, found duplicates.")
      else varnames
    case _ =>
      throw new IllegalArgumentException(
          s"requirement failed: Expected elem to be a variable name or a tuple of variable names, found $elem.")
  }

  /** Removes elem from the scope, as the scope only contains types of free variables */
  def markAsBound(elem: TlaEx): TBuilderInternalState[Unit] = State[TBuilderContext, Unit] { mi: TBuilderContext =>
    val vars = getBoundVarsOrThrow(elem)
    (mi.copy(freeNameScope = mi.freeNameScope -- vars), ())
  }

  /**
   * Some (ternary) operators introduce bound variables (e.g. choose, exists, forall). This method constructs the
   * expressions associated with the operator, and additionally performs shadowing checks and bound-variable tagging.
   */
  def boundVarIntroductionTernary(
      unsafeMethod: (TlaEx, TlaEx, TlaEx) => TlaEx // argument order: (variable, set, expression)
    )(variable: TBuilderInstruction,
      set: TBuilderInstruction,
      expr: TBuilderInstruction): TBuilderInstruction = for {
    usedBefore <- getAllUsed
    boundBefore <- getAllBound
    setEx <- set
    usedInSetOrBefore <- getAllUsed // variable may not appear as bound or free in set
    exprEx <- expr
    boundAfterExpr <- getAllBound // variable may not appear as bound in expr
    usedInScope = (usedInSetOrBefore -- usedBefore) ++ (boundAfterExpr -- boundBefore)
    varEx <- variable
    _ <- markAsBound(varEx)
  } yield {
    val ret = unsafeMethod(varEx, setEx, exprEx)
    val names = getBoundVarsOrThrow(varEx)
    // variable is shadowed iff names \cap usedInScope /= {}
    val shadowed = names.intersect(usedInScope)
    if (shadowed.nonEmpty) throw new TBuilderScopeException(s"Variable shadowing in $ret: ${shadowed.mkString(", ")}.")
    else ret
  }

  /**
   * Some (binary) operators introduce bound variables (e.g. chooseUnbounded, existsUnbounded, forallUnbounded). This
   * method constructs the expressions associated with the operator, and additionally performs shadowing checks and
   * bound-variable tagging.
   */
  def boundVarIntroductionBinary(
      unsafeMethod: (TlaEx, TlaEx) => TlaEx // argument order: (variable, expression)
    )(variable: TBuilderInstruction,
      expr: TBuilderInstruction): TBuilderInstruction = for {
    boundBefore <- getAllBound
    exprEx <- expr
    boundAfterExpr <- getAllBound // variable may not appear as bound in expr
    varEx <- variable
    _ <- markAsBound(varEx)
  } yield {
    val ret = unsafeMethod(varEx, exprEx)
    val names = getBoundVarsOrThrow(varEx)
    // variable is shadowed iff names \cap (boundAfterExpr \ boundBefore) /= {}
    val shadowed = names.intersect(boundAfterExpr -- boundBefore)
    if (shadowed.nonEmpty) throw new TBuilderScopeException(s"Variable shadowing in $ret: ${shadowed.mkString(", ")}.")
    else ret
  }

  /**
   * Some (variadic) operators introduce bound variables (e.g. map, funDef). This method constructs the expressions
   * associated with the operator, and additionally performs shadowing checks and bound-variable tagging.
   */
  def boundVarIntroductionVariadic(
      unsafeMethod: (TlaEx, Seq[(TlaEx, TlaEx)]) => TlaEx
    )(ex: TBuilderInstruction,
      varSetPairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction = for {
    boundBefore <- getAllBound
    bodyEx <- ex
    boundAfterBodyEx <- getAllBound // variables may not appear as bound in bodyEx
    pairs <- varSetPairs.foldLeft(Seq.empty[(TlaEx, TlaEx)].point[TBuilderInternalState]) {
      case (cmp, (variable, set)) =>
        for {
          seq <- cmp
          usedBefore <- getAllUsed
          setEx <- set
          usedInSetOrBefore <- getAllUsed // variable_i may not appear as bound or free in set_i
          usedInScope = (usedInSetOrBefore -- usedBefore) ++ (boundAfterBodyEx -- boundBefore)
          varEx <- variable
          // we delay marking as bound, to not interfere with other variable-set pairs
        } yield {
          val names = getBoundVarsOrThrow(varEx)
          // variable_i is shadowed iff names \cap usedInScope /= {}
          val shadowed = names.intersect(usedInScope)
          if (shadowed.nonEmpty) {
            val source = if (names.intersect(boundAfterBodyEx).nonEmpty) bodyEx else setEx
            throw new TBuilderScopeException(s"Variable shadowing in $source: ${shadowed.mkString(", ")}.")
          } else seq :+ (varEx, setEx)
        }
    }
    // Mark as bound later
    _ <- buildSeq(pairs.map(pa => markAsBound(pa._1)))
  } yield unsafeMethod(bodyEx, pairs)

  /**
   * Convenience shorthand to access the set of used names. May return different values at different places, depending
   * on the internal state.
   */
  def getAllUsed: TBuilderInternalState[Set[String]] =
    gets[TBuilderContext, Set[String]] { _.usedNames }

  /**
   * Convenience shorthand to access the set of bound names. May return different values at different places, depending
   * on the internal state.
   */
  def getAllBound: TBuilderInternalState[Set[String]] =
    gets[TBuilderContext, Set[String]] { ctx => ctx.usedNames -- ctx.freeNameScope.keySet }

  /**
   * Given a sequence of computations, generates a computation that runs them in order and accumulates results to a
   * sequence of values
   */
  def buildSeq[T](args: Seq[TBuilderInternalState[T]]): TBuilderInternalState[Seq[T]] =
    args.foldLeft(Seq.empty[T].point[TBuilderInternalState]) { case (seq, arg) =>
      for {
        seqEx <- seq
        argEx <- arg
      } yield seqEx :+ argEx
    }

  /** Lifts a binary unsafe method to a [[TBuilderInstruction]] method */
  def binaryFromUnsafe(
      x: TBuilderInstruction,
      y: TBuilderInstruction,
    )(unsafeMethod: (TlaEx, TlaEx) => TlaEx): TBuilderInstruction = for {
    xEx <- x
    yEx <- y
  } yield unsafeMethod(xEx, yEx)

  /** Lifts a ternary unsafe method to a TBuilderInstruction method */
  def ternaryFromUnsafe(
      x: TBuilderInstruction,
      y: TBuilderInstruction,
      z: TBuilderInstruction,
    )(unsafeMethod: (TlaEx, TlaEx, TlaEx) => TlaEx): TBuilderInstruction = for {
    xEx <- x
    yEx <- y
    zEx <- z
  } yield unsafeMethod(xEx, yEx, zEx)

  /** generates a BuilderTypeException wrapped in a Left, containing the given message */
  def leftTypeException(msg: String): TypeComputationResult = Left(new TBuilderTypeException(msg))

  /** Generates a (total) signature from a partial one, by returning a Left outside the domain */
  def completePartial(name: String, partialSig: PartialSignature): Signature = {
    def onElse(badArgs: Seq[TlaType1]): TypeComputationResult =
      leftTypeException(
          s"Operator $name cannot be applied to arguments of types (${badArgs.mkString(", ")})"
      )

    { args =>
      partialSig.applyOrElse(
          args,
          onElse,
      )
    }
  }

  /** Wraps a signature with an arity check, to throw a more precise exception on arity mismatch */
  def checkForArityException(
      name: String,
      arity: OperArity,
      partialSig: PartialSignature): Signature = {
    case args if arity.cond(args.size) => completePartial(name, partialSig)(args)
    case args                          => leftTypeException(s"$name expects $arity arguments, found: ${args.size}")
  }

  /**
   * Creates a SignatureMap entry from an operator (key), where the signature (value) is lifted from `partialSignature`
   * via `checkForArityException` (with arity derived from the operator).
   * @see
   *   [[checkForArityException]]
   */
  def signatureMapEntry(oper: TlaOper, partialSignature: PartialSignature): (TlaOper, Signature) =
    oper -> checkForArityException(oper.name, oper.arity, partialSignature)

}
