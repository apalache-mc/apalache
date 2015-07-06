package at.forsyte.tlair

/**
 * A location in a text file characterized by line number and column.
 *
 * @author konnov
 */
class Loc(val lineno: Int, val colno: Int) extends Ordered[Loc] {
  /**
   * Compare locations as a natural order on (line, column)
   * @param that the object to compare to
   * @return -1 when less than, 0 when equal, and 1 otherwise
   */
  override def compare(that: Loc): Int =
    if (this.lineno == that.lineno)
      Integer.compare(this.colno, that.colno)
    else
      Integer.compare(this.lineno, that.lineno)
}

object Loc {
  def apply(line: Int, col: Int): Loc = new Loc(line, col)
}