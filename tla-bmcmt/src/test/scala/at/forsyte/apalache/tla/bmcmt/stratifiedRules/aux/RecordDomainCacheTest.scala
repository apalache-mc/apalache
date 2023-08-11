package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

import at.forsyte.apalache.tla.bmcmt.PureArena
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches.{RecordDomainCache, UninterpretedLiteralCache}
import at.forsyte.apalache.tla.lir.{StrT1, TlaType1}
import at.forsyte.apalache.tla.types.{tla, ModelValueHandler}
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import scala.collection.immutable.SortedSet

@RunWith(classOf[JUnitRunner])
class RecordDomainCacheTest extends AnyFunSuite with BeforeAndAfterEach {

  var ulitCache: UninterpretedLiteralCache = new UninterpretedLiteralCache
  var cache: RecordDomainCache = new RecordDomainCache(ulitCache)

  def tpAndIdx(s: String): (TlaType1, String) = {
    val (utype, idx) = ModelValueHandler.typeAndIndex(s).getOrElse((StrT1, s))
    (utype, idx)
  }

  override def beforeEach(): Unit = {
    ulitCache = new UninterpretedLiteralCache
    cache = new RecordDomainCache(ulitCache)
  }

  test("Cache returns stored values after the first call to getOrCreate") {
    val keys: SortedSet[String] = SortedSet("a", "b", "c")

    val arena = PureArena.empty

    // No cached value for the pair
    assert(cache.get(keys).isEmpty)

    val (newArena, (cell, elemCells)) = cache.getOrCreate(arena, keys)

    // set is now cached, arena has changed
    assert(cache.get(keys).nonEmpty && newArena != arena)

    val (newArena2, (cell2, elemCells2)) = cache.getOrCreate(newArena, keys)

    // 2nd call returns the _same_ arena and the previously computed cells
    assert(newArena == newArena2 && cell == cell2 && elemCells == elemCells2)
  }

  test("Constraints are only added when addConstraintsForElem is explicitly called, and only once per value") {
    val mockCtx: MockZ3SolverContext = new MockZ3SolverContext

    val k1: SortedSet[String] = SortedSet.empty[String]
    val k2: SortedSet[String] = SortedSet("a", "b")
    val k3: SortedSet[String] = SortedSet("a", "c")

    val a0 = PureArena.empty
    val (a1, (cell1, elemCells1)) = cache.getOrCreate(a0, k1)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a0, k1)
    cache.getOrCreate(a0, k1)
    val (a2, (cell2, elemCells2)) = cache.getOrCreate(a1, k2)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a1, k2)
    cache.getOrCreate(a1, k2)
    val (_, (cell3, elemCells3)) = cache.getOrCreate(a2, k3)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a2, k3)
    cache.getOrCreate(a2, k3)

    assert(mockCtx.constraints.isEmpty)

    // "a" is a member of 2 sets, but it only gets cached into 1 cell
    assert(ulitCache.values().size == 3)

    cache.addAllConstraints(mockCtx)

    // Dependent caches don't discharge constraints unless called, so we should have 0 constraints
    // from UninterpretedLiteralCache, only the ones from the domain cache
    assert(mockCtx.constraints.size == k1.size + k2.size + k3.size)
    assert(
        elemCells1.forall { c =>
          mockCtx.constraints.contains(tla.in(c.toBuilder, cell1.toBuilder).build)
        }
    )
    assert(
        elemCells2.forall { c =>
          mockCtx.constraints.contains(tla.in(c.toBuilder, cell2.toBuilder).build)
        }
    )
    assert(
        elemCells3.forall { c =>
          mockCtx.constraints.contains(tla.in(c.toBuilder, cell3.toBuilder).build)
        }
    )
  }

}
