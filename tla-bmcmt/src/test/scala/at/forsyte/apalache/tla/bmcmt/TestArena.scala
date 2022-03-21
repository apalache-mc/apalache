package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, FinSetT, UnknownT}
import org.scalatest.funsuite.AnyFunSuite

/**
 * [[Arena]] tests. Override [[AnyFunSuite.withFixture()]] to set up specific solver contexts (e.g., for different
 * encodings).
 */
trait TestArena extends AnyFunSuite {
  protected var solver: Z3SolverContext = _

  test("create cells") {
    val emptyArena = Arena.create(solver)
    val arena = emptyArena.appendCell(UnknownT())
    assert(emptyArena.cellCount + 1 == arena.cellCount)
    assert(UnknownT() == arena.topCell.cellType)
    val arena2 = arena.appendCell(BoolT())
    assert(emptyArena.cellCount + 2 == arena2.cellCount)
    assert(BoolT() == arena2.topCell.cellType)
  }

  test("add 'has' edges") {
    val arena = Arena.create(solver).appendCell(FinSetT(UnknownT()))
    val set = arena.topCell
    val arena2 = arena.appendCell(BoolT())
    val elem = arena2.topCell
    val arena3 = arena2.appendHas(set, elem)
    assert(List(elem) == arena3.getHas(set))
  }

  test("BOOLEAN has FALSE and TRUE") {
    val arena = Arena.create(solver)
    assert(List(arena.cellFalse(), arena.cellTrue()) == arena.getHas(arena.cellBooleanSet()))
  }
}
