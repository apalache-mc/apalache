package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp.src.SourceLocation
import at.forsyte.apalache.tla.lir.UID
import at.forsyte.apalache.tla.lir.src.{SourceLocation, SourcePosition, SourceRegion}
import at.forsyte.apalache.tla.lir.storage.SourceLocator
import com.typesafe.scalalogging.LazyLogging

class TransitionOrder(sourceLocator: SourceLocator) extends LazyLogging {

  /**
   * Sorts the transitions lexicographically on the source code information of assignments
   */
  def sortBySource(transitions: Seq[SymbTrans]): Seq[SymbTrans] = {
    transitions sortWith transLT
  }

  private type orderTup = (String, Int, Int)

  private def tupProjection(s: SourceLocation): orderTup =
    (s.filename, s.region.start.line, s.region.start.column)

  /**
   * a < b iff
   *
   * (a.filename, a.region.start.line, a.region.start.column)
   * <
   * (b.filename, b.region.start.line, b.region.start.column)
   */
  private def locCmp(a: SourceLocation, b: SourceLocation): Int =
    Ordering[orderTup].compare(tupProjection(a), tupProjection(b))

  private def locLT(a: SourceLocation, b: SourceLocation): Boolean =
    Ordering[orderTup].lt(tupProjection(a), tupProjection(b))

  private def dropPrefixZeros(s: Seq[Int]): Int = s match {
    case Nil      => 0
    case v +: Nil => v
    case v +: vs =>
      if (v != 0)
        v
      else
        dropPrefixZeros(vs)
  }

  private def lexCmpSeqs[T](cmpFun: (T, T) => Int)(a: Seq[T], b: Seq[T]): Int =
    dropPrefixZeros(
        a.zip(b) map { case (x, y) => cmpFun(x, y) }
    )

  /**
   * we assume |a| = |b|, as is the case when a and b are assignment selections
   */
  private def seqLocLT(a: Seq[SourceLocation], b: Seq[SourceLocation]): Boolean =
    lexCmpSeqs(locCmp)(a, b) < 0

  private def getSortedLocs(s: SymbTrans): Seq[SourceLocation] = {
    def findLoc(uid: UID): SourceLocation = {
      sourceLocator.sourceOf(uid) match {
        case Some(loc) => loc
        case None      =>
          // degrading without throwing an exception
          logger.warn(s"Missing source location for UID = $UID")
          SourceLocation("unknown", new SourceRegion(SourcePosition(1), SourcePosition(2)))
      }
    }

    s._1 map findLoc sortWith locLT
  }

  private def transLT(a: SymbTrans, b: SymbTrans): Boolean = seqLocLT(getSortedLocs(a), getSortedLocs(b))
}
