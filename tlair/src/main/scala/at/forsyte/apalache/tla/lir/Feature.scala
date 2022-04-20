package at.forsyte.apalache.tla.lir

/**
 * An experimental feature.
 */
sealed trait Feature {}

/**
 * Enable rows, new records, and variants, as described in <a
 * href="https://github.com/informalsystems/apalache/blob/unstable/docs/src/adr/014adr-precise-records.md">ADR-014</a>.
 */
case class RowsFeature() extends Feature
