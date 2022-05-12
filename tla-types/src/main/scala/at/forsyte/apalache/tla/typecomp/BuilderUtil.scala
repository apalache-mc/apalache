package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, Typed}
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
    (mi.copy(mi.nameScope - elem.asInstanceOf[NameEx].name), ())
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

  /** Lifts a binary raw method to a BuilderWrapper method */
  def binaryFromUnsafe(
      x: TBuilderInstruction,
      y: TBuilderInstruction,
    )(unsafeMethod: (TlaEx, TlaEx) => TlaEx): TBuilderInstruction = for {
    xEx <- x
    yEx <- y
  } yield unsafeMethod(xEx, yEx)

  /** generates a BuilderTypeException wrapped in a Left, containing the given message */
  def throwMsg(msg: String): TypeComputationResult = Left(new TBuilderTypeException(msg))
}
