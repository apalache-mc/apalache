package at.forsyte.apalache.tla.lir.src

/**
 * This class captures a region in a text file.
 *
 * @param start
 *   the starting position
 * @param end
 *   the ending position, inclusive
 * @author
 *   Igor Konnov, Thomas Pani
 */
class SourceRegion(val start: SourcePosition, val end: SourcePosition) {
  def isInside(larger: SourceRegion): Boolean = {
    start >= larger.start && end <= larger.end
  }

  def contains(smaller: SourceRegion): Boolean = {
    smaller.isInside(this)
  }

  def isIntersecting(another: SourceRegion): Boolean = {
    val maxStart = Seq(start, another.start).max
    val minEnd = Seq(end, another.end).min
    maxStart <= minEnd
  }

  override def toString: String = s"${start}-${end}"

  def canEqual(other: Any): Boolean = other.isInstanceOf[SourceRegion]

  override def equals(other: Any): Boolean = other match {
    case that: SourceRegion =>
      that.canEqual(this) &&
      start.equals(that.start) &&
      end.equals(that.end)
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(start, end)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}

object SourceRegion {
  def apply(start: SourcePosition, end: SourcePosition): SourceRegion = {
    new SourceRegion(start, end)
  }

  def apply(
      lineStart: Int,
      columnStart: Int,
      lineEnd: Int,
      columnEnd: Int): SourceRegion = {
    new SourceRegion(SourcePosition(lineStart, columnStart), SourcePosition(lineEnd, columnEnd))
  }
}
