package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaActionOper, TlaOper}
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

    val ex = tla.and(tla.eql(n_x, 1), tla.eql(n_y, 2), tla.eql(n_z, 3))

    val ret = reordering.reorder(ex)

    assert(ex == ret)

  }

  test("Reordering with an x => x.ID rankingFn : NoOp") {
    val rankingFn: TlaEx => T = ex => Some(ex.ID.id.toInt)

    val reordering = mkReordering(rankingFn)

    val ex = tla.and(tla.eql(n_x, 1), tla.eql(n_y, 2), tla.eql(n_z, 3))

    val ret = reordering.reorder(ex)

    assert(ex == ret)

  }

  test("Reordering with an x => -x.ID rankingFn : Inverse order") {
    val rankingFn: TlaEx => T = ex => Some(-ex.ID.id.toInt)

    val reordering = mkReordering(rankingFn)

    val ex = tla.and(tla.eql(n_x, 1), tla.eql(n_y, 2), tla.eql(n_z, 3))
    val expected = tla.and(tla.eql(n_z, 3), tla.eql(n_y, 2), tla.eql(n_x, 1))

    val ret = reordering.reorder(ex)

    assert(ret == expected)

  }

  test("Reordering z assignments to the front") {
    val rankingFn: TlaEx => T = {
      case OperEx(BmcOper.assign, OperEx(TlaActionOper.prime, NameEx("z")), _) => Some(0)
      case _                                                                   => None
    }

    val reordering = mkReordering(rankingFn)

    val ex = tla.and(tla.assignPrime(n_x, 1), tla.assignPrime(n_y, 2), tla.assignPrime(n_z, 3))
    val expected = tla.and(tla.assignPrime(n_z, 3), tla.assignPrime(n_x, 1), tla.assignPrime(n_y, 2))

    val ret = reordering.reorder(ex)

    assert(ret == expected)

  }

}
