package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.oper.{OperArity, TlaOper}
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

  /** Removes elem from the scope, as the scope only contains types of free variables */
  def markAsBound(elem: TlaEx): TBuilderInternalState[Unit] = State[TBuilderContext, Unit] { mi: TBuilderContext =>
    require(elem.isInstanceOf[NameEx])
    (mi.copy(freeNameScope = mi.freeNameScope - elem.asInstanceOf[NameEx].name), ())
  }

  /**
   * Some (ternary) operators introduce bound variables (e.g. choose, exists, forall). This method constructs the
   * expressions associated with the operator, and additionally performs shadowing checks and bound-variable tagging.
   */
  def boundVarIntroductionTernary(
      rawMethod: (TlaEx, TlaEx, TlaEx) => TlaEx // argument order: (variable, set, expression)
    )(variable: TBuilderInstruction,
      set: TBuilderInstruction,
      expr: TBuilderInstruction): TBuilderInstruction = for {
    setEx <- set
    usedInSet <- allUsed // variable may not appear as bound or free in set
    exprEx <- expr
    boundAfterExpr <- allBound // variable may not appear as bound in expr
    varEx <- variable
    _ <- markAsBound(varEx)
    // variable is shadowed iff boundAfterVar \subseteq usedInSet \union boundAfrerExpr
    boundAfterVar <- allBound
  } yield {
    val ret = rawMethod(varEx, setEx, exprEx)
    if (boundAfterVar.subsetOf(usedInSet.union(boundAfterExpr))) {
      val name = varEx.asInstanceOf[NameEx].name // assume ret would have already thrown if not NameEx
      throw new TBuilderScopeException(s"Variable $name is shadowed in $ret.")
    } else ret
  }

  /**
   * Some (binary) operators introduce bound variables (e.g. chooseUnbounded, existsUnbounded, forallUnbounded). This
   * method constructs the expressions associated with the operator, and additionally performs shadowing checks and
   * bound-variable tagging.
   */
  def boundVarIntroductionBinary(
      rawMethod: (TlaEx, TlaEx) => TlaEx // argument order: (variable, expression)
    )(variable: TBuilderInstruction,
      expr: TBuilderInstruction): TBuilderInstruction = for {
    exprEx <- expr
    boundAfterExpr <- allBound // variable may not appear as bound in expr
    varEx <- variable
    _ <- markAsBound(varEx)
    // variable is shadowed iff boundAfterVar \subseteq boundAfterExpr
    boundAfterVar <- allBound
  } yield {
    val ret = rawMethod(varEx, exprEx)
    if (boundAfterVar.subsetOf(boundAfterExpr)) {
      val name = varEx.asInstanceOf[NameEx].name // assume ret would have already thrown if not NameEx
      throw new TBuilderScopeException(s"Variable $name is shadowed in $ret.")
    } else ret
  }

  /**
   * Some (variadic) operators introduce bound variables (e.g. map, funDef). This method constructs the expressions
   * associated with the operator, and additionally performs shadowing checks and bound-variable tagging.
   */
  def boundVarIntroductionVariadic(
      rawMethod: (TlaEx, Seq[(TlaEx, TlaEx)]) => TlaEx
    )(ex: TBuilderInstruction,
      varSetPairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction = for {
    bodyEx <- ex
    boundAfterBodyEx <- allBound // variables may not appear as bound in bodyEx
    pairs <- varSetPairs.foldLeft(Seq.empty[(TlaEx, TlaEx)].point[TBuilderInternalState]) {
      case (cmp, (variable, set)) =>
        for {
          seq <- cmp
          setEx <- set
          usedInSet <- allUsed // variable_i may not appear as bound or free in set_i
          varEx <- variable
          _ = require(varEx.isInstanceOf[NameEx])
          _ <- markAsBound(varEx)
          // variable_i is shadowed iff boundAfterVar \subseteq usedInSet \union boundAfterBodyEx
          boundAfterVar <- allBound
        } yield
          if (boundAfterVar.subsetOf(usedInSet.union(boundAfterBodyEx))) {
            throw new TBuilderScopeException(s"Variable $varEx is shadowed in $bodyEx or $setEx.")
          } else seq :+ (varEx, setEx)
    }
  } yield rawMethod(bodyEx, pairs)

  /** Convenience shorthand to access the set of used names. */
  def allUsed: TBuilderInternalState[Set[String]] =
    gets[TBuilderContext, Set[String]] { _.usedNames }

  /** Convenience shorthand to access the set of bound names. */
  def allBound: TBuilderInternalState[Set[String]] =
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
