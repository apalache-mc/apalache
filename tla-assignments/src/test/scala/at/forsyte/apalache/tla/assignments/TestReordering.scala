package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper, TlaOper}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TestingPredefs, TlaEx}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestReordering extends FunSuite with TestingPredefs {

  type T = Option[Int]

  def mkReordering(fn: TlaEx => T): Reordering[T] =
    new Reordering[T](Reordering.IntOptOrdering, fn, TrackerWithListeners())

  test("Reordering with a constant rankingFn : NoOp") {
    val rankingFn: TlaEx => T = _ => None

    val reordering = mkReordering(rankingFn)

    val ex = tla.and(tla.eql(n_x, tla.int(1)), tla.eql(n_y, tla.int(2)), tla.eql(n_z, tla.int(3))).untyped()

    val ret = reordering.reorder(ex)

    assert(ex == ret)

  }

  test("Reordering with an x => x.ID rankingFn : NoOp") {
    val rankingFn: TlaEx => T = ex => Some(ex.ID.id.toInt)

    val reordering = mkReordering(rankingFn)

    val ex = tla.and(tla.eql(n_x, tla.int(1)), tla.eql(n_y, tla.int(2)), tla.eql(n_z, tla.int(3))).untyped()

    val ret = reordering.reorder(ex)

    assert(ex == ret)

  }

  test("Reordering with an x => -x.ID rankingFn : Inverse order") {
    val rankingFn: TlaEx => T = ex => Some(-ex.ID.id.toInt)

    val reordering = mkReordering(rankingFn)

    val ex = tla.and(tla.eql(n_x, tla.int(1)), tla.eql(n_y, tla.int(2)), tla.eql(n_z, tla.int(3))).untyped()
    val expected = tla.and(tla.eql(n_z, tla.int(3)), tla.eql(n_y, tla.int(2)), tla.eql(n_x, tla.int(1))).untyped()

    val ret = reordering.reorder(ex)

    assert(ret == expected)

  }

  test("Reordering z assignments to the front") {
    val rankingFn: TlaEx => T = {
      case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx("z")), _) => Some(0)
      case _                                                                        => None
    }

    val reordering = mkReordering(rankingFn)

    val ex = tla
      .and(tla.assignPrime(n_x, tla.int(1)), tla.assignPrime(n_y, tla.int(2)), tla.assignPrime(n_z, tla.int(3)))
      .untyped()
    val expected = tla
      .and(tla.assignPrime(n_z, tla.int(3)), tla.assignPrime(n_x, tla.int(1)), tla.assignPrime(n_y, tla.int(2)))
      .untyped()

    val ret = reordering.reorder(ex)

    assert(ret == expected)

  }

}
