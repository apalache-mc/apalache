package at.forsyte.apalache.tla.imp.src

/**
  * An object of this class represents a position in a text file.
  * Instead of the standard representation of a position as a (line, column), we keep it as line * MAX_WIDTH + column,
  * where MAX_WIDTH is the length of the longest possible line. Whenever a longer column value is given, it is truncated.
  */
class SourcePosition(val offset: Int) {
  /**
    * Get the line number of the position, starting with 1.
    * @return the line number
    */
  def line: Int = 1 + offset / SourcePosition.MAX_WIDTH

  /** Get the column, starting with 1 and up to SourcePosition.MAX_WIDTH */
  def column: Int = 1 + offset % SourcePosition.MAX_WIDTH

  override def toString: String = {
    line + ":" + column
  }


  def canEqual(other: Any): Boolean = other.isInstanceOf[SourcePosition]

  override def equals(other: Any): Boolean = other match {
    case that: SourcePosition =>
      (that canEqual this) &&
        offset == that.offset
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(offset)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}

object SourcePosition {
  /**
    * The maximal length of a text line. We can safely assume that human-produced code does not have lines longer
    * than that. If you generate you code, think of introducing line breaks.
    */
  val MAX_WIDTH = 1000

  def apply(offset: Int): SourcePosition = {
    new SourcePosition(offset)
  }

  def apply(line: Int, column: Int): SourcePosition = {
    val truncatedColumn = if (column <= MAX_WIDTH + 1) column - 1 else MAX_WIDTH
    new SourcePosition((line - 1) * MAX_WIDTH + truncatedColumn)
  }
}
