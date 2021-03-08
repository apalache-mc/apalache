package at.forsyte.apalache.tla.bmcmt.types.eager

import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.UID

import scala.collection.immutable.{Map, SortedMap}

/**
 * A snapshot of TrivialTypeFinder that can be recovered into a new TrivialTypeFinder.
 * All intermediate context are squashed into a single context.
 *
 * @author Igor Konnov
 */
class TrivialTypeSnapshot(val typeAnnotations: Map[UID, CellT], val varTypes: SortedMap[String, CellT]) {}
