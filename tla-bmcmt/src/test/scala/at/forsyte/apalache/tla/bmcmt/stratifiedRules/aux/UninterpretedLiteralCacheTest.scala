package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

import at.forsyte.apalache.tla.bmcmt.PureArena
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches.UninterpretedLiteralCache
import at.forsyte.apalache.tla.lir.StrT1
import at.forsyte.apalache.tla.types.{tla, ModelValueHandler}
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class UninterpretedLiteralCacheTest extends AnyFunSuite with BeforeAndAfterEach {

  var cache: UninterpretedLiteralCache = new UninterpretedLiteralCache

  def tpAndIdx(s: String): (String, String) = {
    val (utype, idx) = ModelValueHandler.typeAndIndex(s).getOrElse((StrT1, s))
    (utype.toString, idx)
  }

  override def beforeEach(): Unit = {
    cache = new UninterpretedLiteralCache
  }

  test("Cache returns stored values after the first call to getOrCreate") {
    val str: String = "idx"

    val utypeAndIdx = tpAndIdx(str)

    val arena = PureArena.empty

    // No cached value for the pair
    assert(cache.get(utypeAndIdx).isEmpty)

    val (newArena, iCell) = cache.getOrCreate(arena, utypeAndIdx)

    // pair now cached, arena has changed
    assert(cache.get(utypeAndIdx).nonEmpty && newArena != arena)

    val (newArena2, iCell2) = cache.getOrCreate(newArena, utypeAndIdx)

    // 2nd call returns the _same_ arena and the previously computed cell
    assert(newArena == newArena2 && iCell == iCell2)
  }

  test("Same index of different types is cached separately") {
    val str1: String = "idx"
    val str2: String = "idx_OF_A"
    val str3: String = "idx_OF_B"

    val pa1 = tpAndIdx(str1)
    val pa2 = tpAndIdx(str2)
    val pa3 = tpAndIdx(str3)

    val arena = PureArena.empty

    val (newArena1, cell1) = cache.getOrCreate(arena, pa1)

    assert(arena != newArena1)

    val (newArena2, cell2) = cache.getOrCreate(newArena1, pa2)

    assert(newArena2 != newArena1 && cell2 != cell1)

    val (newArena3, cell3) = cache.getOrCreate(newArena2, pa3)

    assert(newArena3 != newArena2 && cell3 != cell2)
  }

  test("Constraints are only added when addAllConstraints is explicitly called, and only once per value") {
    val mockCtx: MockZ3SolverContext = new MockZ3SolverContext

    val str1: String = "1_OF_A"
    val str2: String = "2_OF_A"
    val str3: String = "3_OF_A"

    val pa1 = tpAndIdx(str1)
    val pa2 = tpAndIdx(str2)
    val pa3 = tpAndIdx(str3)

    val a0 = PureArena.empty
    val (a1, c1) = cache.getOrCreate(a0, pa1)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a0, pa1)
    cache.getOrCreate(a0, pa1)
    val (a2, c2) = cache.getOrCreate(a1, pa2)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a1, pa2)
    cache.getOrCreate(a1, pa2)
    val (_, c3) = cache.getOrCreate(a2, pa3)
    // Some extra calls, which shouldn't affect constraint generation
    cache.getOrCreate(a2, pa3)
    cache.getOrCreate(a2, pa3)

    assert(mockCtx.constraints.isEmpty)

    cache.addAllConstraints(mockCtx)

    // Due to the optimized `addAllConstraints` override, we only have 1 "distinct"
    assert(mockCtx.constraints == Seq(
        tla.distinct(c1.toBuilder, c2.toBuilder, c3.toBuilder).build
    ))
  }

}
