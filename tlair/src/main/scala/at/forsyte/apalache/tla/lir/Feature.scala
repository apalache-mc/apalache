package at.forsyte.apalache.tla.lir

/**
 * An experimental feature.
 */
sealed trait Feature {
  val name: String
  val description: String
}

/**
 * Enable rows, new records, and variants, as described in <a
 * href="https://github.com/informalsystems/apalache/blob/unstable/docs/src/adr/014adr-precise-records.md">ADR-014</a>.
 */
case class RowsFeature(
    name: String = "rows",
    description: String = "enable row typing as explained in ADR-014")
    extends Feature

object Feature {

  /**
   * A list of all supported features.
   *
   * This provides the source of truth for all valid feature names and descriptions.
   */
  val all = List(RowsFeature())

  val fromString: String => Option[Feature] = str => all.find(_.name == str)
}
