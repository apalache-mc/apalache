package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolType, FinSetType, UnknownType}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestArena extends FunSuite {
  test("create cells") {
    val solverContext = new Z3SolverContext()
    val emptyArena = Arena.create(solverContext)
    val arena = emptyArena.appendCell(UnknownType())
    assert(emptyArena.cellCount + 1 == arena.cellCount)
    assert(UnknownType() == arena.topCell.cellType)
    val arena2 = arena.appendCell(BoolType())
    assert(emptyArena.cellCount + 2 == arena2.cellCount)
    assert(BoolType() == arena2.topCell.cellType)
  }

  test("add 'has' edges") {
    val solverContext = new Z3SolverContext()
    val arena = Arena.create(solverContext).appendCell(FinSetType(UnknownType()))
    val set = arena.topCell
    val arena2 = arena.appendCell(BoolType())
    val elem = arena2.topCell
    val arena3 = arena2.appendHas(set, elem)
    assert(List(elem) == arena3.getHas(set))
  }

  test("BOOLEAN has FALSE and TRUE") {
    val solverContext = new Z3SolverContext()
    val arena = Arena.create(solverContext)
    val boolean = arena.cellBoolean()
    assert(List(arena.cellFalse(), arena.cellTrue()) == arena.getHas(arena.cellBoolean()))
  }
}
