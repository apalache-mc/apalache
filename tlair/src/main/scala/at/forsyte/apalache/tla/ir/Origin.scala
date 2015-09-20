package at.forsyte.apalache.tla.ir

/**
 * Data on the symbol origin
 *
 * @author konnov
 */
class Origin(
  val level: Int,
  val filename: String,
  val locRange: LocRange
)
