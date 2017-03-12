package at.forsyte.apalache.tla.obsolete.ir

/**
 * Data on the symbol origin
 *
 * @author konnov
 */
class Origin(
  val uid: Int,
  val level: Int,
  val filename: String,
  val locRange: LocRange
)
