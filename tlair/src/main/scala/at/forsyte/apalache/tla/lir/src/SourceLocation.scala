package at.forsyte.apalache.tla.lir.src

/**
 * A pointer to the source location, that is, the module name and the source region. It is very much like
 * tla2tools.Location, but it is not using UniqueString. To save space, use the singleton constructor, which
 * internalizes strings.
 *
 * @author
 *   Igor Konnov
 */
object SourceLocation {

  /**
   * Construct a source location, internalizing the filename to save space.
   *
   * @param filename
   *   the name of the module the location points into
   * @param region
   *   the region of the source the location points at
   */
  def apply(filename: String, region: SourceRegion): SourceLocation = {
    new SourceLocation(filename.intern(), region)
  }
}

class SourceLocation(val filename: String, val region: SourceRegion) {
  override def toString: String = filename + ".tla:" + region

  def canEqual(other: Any): Boolean = other.isInstanceOf[SourceLocation]

  override def equals(other: Any): Boolean = other match {
    case that: SourceLocation =>
      (that.canEqual(this)) &&
      filename == that.filename &&
      region == that.region
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(filename, region)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}
