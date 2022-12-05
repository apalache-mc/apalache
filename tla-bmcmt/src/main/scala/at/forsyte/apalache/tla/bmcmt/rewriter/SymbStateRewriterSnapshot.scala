package at.forsyte.apalache.tla.bmcmt.rewriter

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.analyses.ExprGrade
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.caches.{AbstractCacheSnapshot, SimpleCacheSnapshot}
import at.forsyte.apalache.tla.lir.{TlaEx, TlaType1}

import scala.collection.immutable.SortedSet

class SymbStateRewriterSnapshot(
    val intValueCacheSnapshot: AbstractCacheSnapshot[PureArenaAdapter, BigInt, ArenaCell],
    val intRangeCacheSnapshot: AbstractCacheSnapshot[PureArenaAdapter, (Int, Int), ArenaCell],
    val modelValueCacheSnapshot: AbstractCacheSnapshot[PureArenaAdapter, (String, String), ArenaCell],
    val defaultValueCacheSnapshot: AbstractCacheSnapshot[PureArenaAdapter, TlaType1, ArenaCell],
    val recordDomainCache: AbstractCacheSnapshot[PureArenaAdapter, (SortedSet[String], SortedSet[String]), ArenaCell],
    val exprCacheSnapshot: SimpleCacheSnapshot[TlaEx, (TlaEx, ExprGrade.Value)]) {}
