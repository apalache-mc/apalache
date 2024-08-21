package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

import at.forsyte.apalache.tla.bmcmt.PureArena
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches.{IntRangeCache, IntValueCache}
import at.forsyte.apalache.tla.types.{tlaU => tla}
import at.forsyte.apalache.tla.typecomp._
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class IntRangeCacheTest extends AnyFunSuite with BeforeAndAfterEach {

  var intValueCache: IntValueCache = new IntValueCache
  var cache: IntRangeCache = new IntRangeCache(intValueCache)

  override def beforeEach(): Unit = {
    intValueCache = new IntValueCache
    cache = new IntRangeCache(intValueCache)
  }

  test("Cache returns stored values after the first call to getOrCreate") {
    val rangeTup = (1, 5)
    val range = rangeTup._1.to(rangeTup._2)

    val arena = PureArena.empty

    // No cached values
    assert(cache.get(rangeTup).isEmpty)
    assert(range.forall { i => intValueCache.get(i).isEmpty })

    val (newArena, retPair) = cache.getOrCreate(arena, rangeTup)

    // range is now cached, arena has changed
    assert(cache.get(rangeTup).nonEmpty && newArena != arena && range.forall { i => intValueCache.get(i).nonEmpty })

    val (newArena2, retPair2) = cache.getOrCreate(newArena, rangeTup)

    // 2nd call returns the _same_ arena and the previously computed cell
    assert(newArena == newArena2 && retPair == retPair2)
  }

  test("Caching a..b ranges, where a > b, returns the same cell with no elements, for all such a,b") {
    val rangeTup1 = (5, 1)
    val arena = PureArena.empty
    val (newArena, (rCell, cells)) = cache.getOrCreate(arena, rangeTup1)
    assert(cells.isEmpty)

    val rangeTup2 = (1203134, -221)
    val (newArena2, (rCell2, cells2)) = cache.getOrCreate(arena, rangeTup2)
    assert(newArena == newArena2 && rCell == rCell2 && cells == cells2)
  }

  test("Constraints are only added when addConstraintsForElem is explicitly called, and only once per value") {
    val mockCtx: MockZ3SolverContext = new MockZ3SolverContext

    val r1: (Int, Int) = (0, 10)
    val r2: (Int, Int) = (3, 7)
    val r3: (Int, Int) = (100, 0)

    val a0 = PureArena.empty
    val (a1, (cr1, csr1)) = cache.getOrCreate(a0, r1)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a0, r1)
    cache.getOrCreate(a0, r1)
    val (a2, (cr2, csr2)) = cache.getOrCreate(a1, r2)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a1, r2)
    cache.getOrCreate(a1, r2)
    val (_, (cr3, csr3)) = cache.getOrCreate(a2, r3)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a2, r3)
    cache.getOrCreate(a2, r3)

    assert(mockCtx.constraints.isEmpty)

    cache.addAllConstraints(mockCtx)

    // Dependent caches don't discharge constraints unless called, so we should have 0 constraints
    // from IntValueCache, only the ones from the range cache
    def nConstraints(r: (Int, Int)): Int = math.max(r._2 - r._1 + 1, 0)

    assert(mockCtx.constraints.size == nConstraints(r1) + nConstraints(r2) + nConstraints(r3))
    assert(
        csr1.forall { c =>
          mockCtx.constraints.contains(tla.in(c.toBuilder, cr1.toBuilder).build)
        }
    )
    assert(
        csr2.forall { c =>
          mockCtx.constraints.contains(tla.in(c.toBuilder, cr2.toBuilder).build)
        }
    )
    assert(
        csr3.forall { c =>
          mockCtx.constraints.contains(tla.in(c.toBuilder, cr3.toBuilder).build)
        }
    )
  }

}
