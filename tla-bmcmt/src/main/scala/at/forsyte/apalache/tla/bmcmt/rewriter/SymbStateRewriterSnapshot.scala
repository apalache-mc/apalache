package at.forsyte.apalache.tla.bmcmt.rewriter

import at.forsyte.apalache.tla.bmcmt.analyses.ExprGrade
import at.forsyte.apalache.tla.bmcmt.caches.{AbstractCacheSnapshot, SimpleCacheSnapshot}
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell}
import at.forsyte.apalache.tla.lir.TlaEx

import scala.collection.immutable.SortedSet

class SymbStateRewriterSnapshot(val intValueCacheSnapshot: AbstractCacheSnapshot[Arena, BigInt, ArenaCell],
    val intRangeCacheSnapshot: AbstractCacheSnapshot[Arena, (Int, Int), ArenaCell],
    val strValueCacheSnapshot: AbstractCacheSnapshot[Arena, String, ArenaCell],
    val recordDomainCache: AbstractCacheSnapshot[Arena, (SortedSet[String], SortedSet[String]), ArenaCell],
    val exprCacheSnapshot: SimpleCacheSnapshot[TlaEx, (TlaEx, ExprGrade.Value)]) {}
