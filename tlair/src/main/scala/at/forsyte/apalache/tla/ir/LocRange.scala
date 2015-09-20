package at.forsyte.apalache.tla.ir

/**
 * A range in a file.
 * 
 * @author konnov
 */
class LocRange(val start: Loc, val end: Loc) {
  /**
   * Compare non-intersecting ranges
   *
   * @param that the range to compare to
   * @return true iff the ranges do not intersect and this range is before that range
   */
  def before(that: LocRange): Boolean =
    end < that.start

  /**
   * Compare non-intersecting ranges
   *
   * @param that the range to compare to
   * @return true iff the ranges do not intersect and this range is after that range
   */
  def after(that: LocRange): Boolean =
    start > that.end

  /**
   * Check whether two ranges intersect
   *
   * @param that the range to compare to
   * @return true iff the ranges intersect
   */
  def intersects(that: LocRange): Boolean = {
    val (left, right) = if (start < that.start) (this, that) else (that, this)
    left.end >= right.start
  }

  /**
   * Check whether two ranges do not intersect
   *
   * @param that the range to compare to
   * @return true iff the ranges do not intersect
   */
  def not_intersect(that: LocRange): Boolean =
    !this.intersects(that)

  /**
   * Check whether the range is inside of another range
   *
   * @param larger the range that is supposed to be larger
   * @return true iff this range is inside of the larger range (equal borders are included)
   */
  def inside(larger: LocRange): Boolean =
    larger.start <= start && end <= larger.end
}


object LocRange {
  def apply(start: Loc, end: Loc) = new LocRange(start, end)
}