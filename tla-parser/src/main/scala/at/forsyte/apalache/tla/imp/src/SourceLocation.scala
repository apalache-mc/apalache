package at.forsyte.apalache.tla.imp.src

import tla2sany.st.Location
// Aliased, as this object shadows the name `SourceLocation` in term position
import at.forsyte.apalache.tla.lir.src.{SourceLocation => LirSourceLocation, SourceRegion}

/**
 * Construct [[at.forsyte.apalache.tla.lir.src.SourceLocation]] values from SANY locations. The filename-and-region
 * constructor lives in the companion object of the class itself, in `tlair`; only this SANY-specific conversion belongs
 * here, as it is the only part that depends on `tla2tools`.
 */
object SourceLocation {
  def apply(loc: Location): LirSourceLocation = {
    LirSourceLocation(loc.source(), SourceRegion(loc.beginLine(), loc.beginColumn(), loc.endLine(), loc.endColumn()))
  }
}
