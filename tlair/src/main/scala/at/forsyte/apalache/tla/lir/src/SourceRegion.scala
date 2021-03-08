package at.forsyte.apalache.tla.lir.src

/**
 * This class captures a region in a text file. Instead of the standard representation of a position
 * as a (line, column), we keep it as line * MAX_WIDTH + column, where MAX_WIDTH is the length of the longest possible
 * line. Whenever a longer column value is given, it is truncated.
 *
 * @param start the starting position
 * @param end the ending position, inclusive
 * @author Igor Konnov
 */
class SourceRegion(val start: SourcePosition, val end: SourcePosition) {
  def isInside(larger: SourceRegion): Boolean = {
    start.offset >= larger.start.offset && end.offset <= larger.end.offset
  }

  def contains(smaller: SourceRegion): Boolean = {
    smaller.isInside(this)
  }

  def isIntersecting(another: SourceRegion): Boolean = {
    val maxStart = Math.max(start.offset, another.start.offset)
    val minEnd = Math.min(end.offset, another.end.offset)
    maxStart <= minEnd
  }

  override def toString: String = {
    start + "-" + end
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[SourceRegion]

  override def equals(other: Any): Boolean = other match {
    case that: SourceRegion =>
      (that canEqual this) &&
        start == that.start &&
        end == that.end
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

  def apply(lineStart: Int, columnStart: Int, lineEnd: Int, columnEnd: Int): SourceRegion = {
    new SourceRegion(SourcePosition(lineStart, columnStart), SourcePosition(lineEnd, columnEnd))
  }
}
