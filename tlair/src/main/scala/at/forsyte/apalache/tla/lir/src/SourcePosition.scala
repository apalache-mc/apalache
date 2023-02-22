package at.forsyte.apalache.tla.lir.src

/**
 * Represent a position in a text file as a `(line, column)` tuple.
 */
class SourcePosition(val line: Int, val column: Int) extends Ordered[SourcePosition] {
  override def toString: String = s"${line}:${column}"

  def canEqual(other: Any): Boolean = other.isInstanceOf[SourcePosition]

  override def equals(other: Any): Boolean = other match {
    case that: SourcePosition => that.canEqual(this) && this.line == that.line && this.column == that.column
    case _                    => false
  }

  override def hashCode(): Int = {
    line * 31 + column
  }

  override def compare(that: SourcePosition): Int = this.line - that.line match {
    case 0    => this.column - that.column
    case diff => diff
  }
}

object SourcePosition {
  def apply(line: Int, column: Int): SourcePosition = {
    new SourcePosition(line, column)
  }
}
