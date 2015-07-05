package at.forsyte.tlair

/**
 * A location in a text file characterized by line number and column.
 *
 * @author konnov
 */
class Loc(val lineno: Int, val colno: Int) extends Ordered[Loc] {
  override def compare(that: Loc): Int =
    if (this.lineno == that.lineno)
      Integer.compare(this.colno, that.colno)
    else
      Integer.compare(this.lineno, that.lineno)
}
