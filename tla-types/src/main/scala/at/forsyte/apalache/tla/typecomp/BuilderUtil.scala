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
    (mi.copy(nameScope = mi.nameScope - elem.asInstanceOf[NameEx].name), ())
  }

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
