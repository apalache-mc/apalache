package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}
import scalaz._
import scalaz.Scalaz._

/**
 * Utility methods
 *
 * @author
 *   Jure Kukovec
 */
object BuilderUtil {
  def markAsBound(elem: NameEx): InternalState[Unit] = State[MetaInfo, Unit] { mi: MetaInfo =>
    (mi.copy(mi.nameScope - elem.name), ())
  }

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

  // Lifts a binary raw method to a BuilderWrapper method
  def polyadicFromRaw(argsW: Seq[BuilderWrapper])(rawMethod: Seq[TlaEx] => TlaEx): BuilderWrapper =
    buildSeq(argsW).map(rawMethod)

  def throwMsg(msg: String): typeComputationReturn = Left(new BuilderTypeException(msg))
}
