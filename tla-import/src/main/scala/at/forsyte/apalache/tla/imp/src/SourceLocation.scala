package at.forsyte.apalache.tla.imp.src

import tla2sany.st.Location
import at.forsyte.apalache.tla.lir.src._

object SourceLocation {
  def apply(filename: String, region: SourceRegion): SourceLocation = {
    new SourceLocation(filename.intern(), region)
  }

  def apply(loc: Location): SourceLocation = {
    new SourceLocation(loc.source().intern(),
      SourceRegion(loc.beginLine(), loc.beginColumn(), loc.endLine(), loc.endColumn()))
  }
}
