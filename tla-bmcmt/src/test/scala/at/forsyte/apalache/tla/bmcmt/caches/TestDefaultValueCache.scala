package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.io.config.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.RewriterBase
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, StrT1}

/**
 * Unit tests for DefaultValueCache. See #1544 (the cache had a hard-to-debug bug, #1543, but no tests).
 */
trait TestDefaultValueCache extends RewriterBase {
  test("""getOrCreate caches: the same type yields the same cell""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val cache = new DefaultValueCache(rewriter)
    val (arena1, cell1) = cache.getOrCreate(arena, IntT1)
    val (_, cell2) = cache.getOrCreate(arena1, IntT1)
    assert(cell1 == cell2)
    assert(solverContext.sat())
  }

  test("""getOrCreate yields distinct cells for distinct types""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val cache = new DefaultValueCache(rewriter)
    val (arena1, intCell) = cache.getOrCreate(arena, IntT1)
    val (arena2, boolCell) = cache.getOrCreate(arena1, BoolT1)
    val (_, strCell) = cache.getOrCreate(arena2, StrT1)
    assert(Set(intCell, boolCell, strCell).size == 3)
    assert(solverContext.sat())
  }

  test("""get returns the cached cell after getOrCreate, and the cell has the requested type""") {
    rewriterType: SMTEncoding =>
      val rewriter = create(rewriterType)
      val cache = new DefaultValueCache(rewriter)
      assert(cache.get(IntT1).isEmpty)
      val (_, cell) = cache.getOrCreate(arena, IntT1)
      assert(cache.get(IntT1).contains(cell))
      assert(cell.cellType.toTlaType1 == IntT1)
  }
}
