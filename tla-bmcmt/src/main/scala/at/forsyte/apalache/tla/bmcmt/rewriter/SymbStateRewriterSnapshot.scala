package at.forsyte.apalache.tla.bmcmt.rewriter

import at.forsyte.apalache.tla.bmcmt.analyses.ExprGrade
import at.forsyte.apalache.tla.bmcmt.caches.{AbstractCacheSnapshot, SimpleCacheSnapshot}
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, SymbState}
import at.forsyte.apalache.tla.lir.{TlaEx, TlaType1}

import scala.collection.immutable.SortedSet

class SymbStateRewriterSnapshot(
    val intValueCacheSnapshot: AbstractCacheSnapshot[Arena, BigInt, ArenaCell],
    val intRangeCacheSnapshot: AbstractCacheSnapshot[Arena, (Int, Int), ArenaCell],
    val modelValueCacheSnapshot: AbstractCacheSnapshot[Arena, (String, String), ArenaCell],
    val defaultValueCacheSnapshot: AbstractCacheSnapshot[SymbState, TlaType1, ArenaCell],
    val recordDomainCache: AbstractCacheSnapshot[Arena, (SortedSet[String], SortedSet[String]), ArenaCell],
    val exprCacheSnapshot: SimpleCacheSnapshot[TlaEx, (TlaEx, ExprGrade.Value)]) {}
