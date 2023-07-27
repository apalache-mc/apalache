package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

import at.forsyte.apalache.tla.bmcmt.PureArena
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches.IntValueCache
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class IntValueCacheTest extends AnyFunSuite with BeforeAndAfterEach {

  var cache: IntValueCache = new IntValueCache

  override def beforeEach(): Unit = {
    cache = new IntValueCache
  }

  test("Cache returns stored values after the first call to getOrCreate") {
    val i: BigInt = 42

    val arena = PureArena.empty

    // No cached value for i
    assert(cache.get(i).isEmpty)

    val (newArena, iCell) = cache.getOrCreate(arena, i)

    // i now cached, arena has changed
    assert(cache.get(i).nonEmpty && newArena != arena)

    val (newArena2, iCell2) = cache.getOrCreate(newArena, i)

    // 2nd call returns the _same_ arena and the previously computed cell
    assert(newArena == newArena2 && iCell == iCell2)
  }

  test("Constraints are only added when addConstraintsForElem is explicitly called, and only once per value") {
    val mockCtx: MockZ3SolverContext = new MockZ3SolverContext

    val i1: BigInt = 42
    val i2: BigInt = 0

    val a0 = PureArena.empty
    val (a1, ci1) = cache.getOrCreate(a0, i1)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a0, i1)
    cache.getOrCreate(a0, i1)
    val (_, ci2) = cache.getOrCreate(a1, i2)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a1, i2)
    cache.getOrCreate(a1, i2)

    assert(mockCtx.constraints.isEmpty)

    cache.addAllConstraints(mockCtx)

    assert(mockCtx.constraints.size == 2)
    assert(
        mockCtx.constraints.contains(tla.eql(ci1.toBuilder, tla.int(i1)).build)
    )
    assert(
        mockCtx.constraints.contains(tla.eql(ci2.toBuilder, tla.int(i2)).build)
    )

  }

}
