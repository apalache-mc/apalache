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
  def markAsBound(elem: TlaEx): InternalState[Unit] = State[MetaInfo, Unit] { mi: MetaInfo =>
    // If name is now bound, we remove it from the scope
    val newMi = elem match {
      case NameEx(name) =>
        mi.copy(mi.nameScope - name)
      case _ => mi
    }
    (newMi, ())
  }

  // Lifts a binary raw method to a BuilderWrapper method
  def binaryFromRaw(xW: BuilderWrapper, yW: BuilderWrapper)(rawMethod: (TlaEx, TlaEx) => TlaEx): BuilderWrapper = for {
    x <- xW
    y <- yW
  } yield rawMethod(x, y)

  // Lifts a binary raw method to a BuilderWrapper method
  def polyadicFromRaw(argsW: Seq[BuilderWrapper])(rawMethod: Seq[TlaEx] => TlaEx): BuilderWrapper = for {
    args <- argsW.foldLeft(Seq.empty[TlaEx].point[InternalState]) { case (seqW, argW) =>
      for {
        seq <- seqW
        arg <- argW
      } yield seq :+ arg
    }
  } yield rawMethod(args)

  def throwMsg(msg: String): typeComputationReturn = Left(new BuilderTypeException(msg))
}
