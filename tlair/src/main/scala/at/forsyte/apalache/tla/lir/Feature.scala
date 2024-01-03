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
 * href="https://github.com/informalsystems/apalache/blob/main/docs/src/adr/014adr-precise-records.md">ADR-014</a>.
 *
 * [[RowsFeature]] is mutually exclusive to [[ImpreciseRecordsFeature]]. We enable [[RowsFeature]] by default and keep
 * it only for backwards compatibility.
 */
case class RowsFeature(
    name: String = "rows",
    description: String = "enable row typing as explained in ADR-014 (default in versions after 0.29.0)")
    extends Feature {
  override val toString: String = name
}

/**
 * Enable imprecise record types, see <a
 * href="https://apalache.informal.systems/docs/adr/002adr-types.html#15-discussion">the discussion in ADR-002</a>.
 *
 * [[ImpreciseRecordsFeature]] is mutually exclusive with [[RowsFeature]]. It is present only for backwards
 * compatibility.
 */
case class ImpreciseRecordsFeature(
    name: String = "no-rows",
    description: String = "disable row types, make records imprecise (default in versions prior to 0.29.0)")
    extends Feature {
  override val toString: String = name
}

object Feature {

  /**
   * A list of all supported features.
   *
   * This provides the source of truth for all valid feature names and descriptions.
   */
  val all: Seq[Feature] = List(RowsFeature(), ImpreciseRecordsFeature())

  val fromString: String => Option[Feature] = str => all.find(_.name == str)
}
