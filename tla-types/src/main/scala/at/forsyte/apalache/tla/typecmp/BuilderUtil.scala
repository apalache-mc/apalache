package at.forsyte.apalache.tla.typecmp

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

  // Constructs an OperEx expression for oper applied to args. Uses typeCmp to validate args and determine the result type
  def buildInstruction(oper: TlaOper, typeCmp: typeComputation, args: TlaEx*): TlaEx = typeCmp(args) match {
    case Left(err) => throw err
    case Right(typeRes) =>
      OperEx(oper, args: _*)(Typed(typeRes))
  }

  // Removes elem from the scope, as the scope only contains types of free variables
  def markAsBound(elem: NameEx): InternalState[Unit] = State[MetaInfo, Unit] { mi: MetaInfo =>
    (mi.copy(mi.nameScope - elem.name), ())
  }

  // Given a sequence of computations, generates a computation that runs them
  // in order and accumulates results to a sequence of values
  def buildSeq[T](argsW: Seq[InternalState[T]]): InternalState[Seq[T]] =
    argsW.foldLeft(Seq.empty[T].point[InternalState]) { case (seqW, argW) =>
      for {
        seq <- seqW
        arg <- argW
      } yield seq :+ arg
    }

  // Lifts a binary raw method to a BuilderWrapper method
  def binaryFromRaw(xW: BuilderWrapper, yW: BuilderWrapper)(rawMethod: (TlaEx, TlaEx) => TlaEx): BuilderWrapper = for {
    x <- xW
    y <- yW
  } yield rawMethod(x, y)

  // generates a BuilderTypeException wrapped in a Left, containing the given message
  def throwMsg(msg: String): typeComputationReturn = Left(new BuilderTypeException(msg))
}
