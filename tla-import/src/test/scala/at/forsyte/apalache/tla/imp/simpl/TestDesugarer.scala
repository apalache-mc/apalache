package at.forsyte.apalache.tla.imp.simpl

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalactic.TripleEqualsSupport
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDesugarer extends FunSuite with BeforeAndAfterEach {
  private var desugarer = new Desugarer(TrackerWithListeners())

  override def beforeEach(): Unit = {
    desugarer = new Desugarer(TrackerWithListeners())
  }

  test("chain 2 excepts") {
    // [f EXCEPT ![i][j] = e]
    val highCalories =
      tla.except(tla.name("f"), tla.tuple(tla.name("i"), tla.name("j")), tla.name("e"))
    val sugarFree = desugarer.transform(highCalories)
    // becomes [ f EXCEPT ![i] = [f[i] EXCEPT ![j] = e] ]
    val expected =
      tla.except(
        tla.name("f"),
        tla.tuple(tla.name("i")),
        tla.except(
          tla.appFun(tla.name("f"), tla.name("i")),
          tla.tuple(tla.name("j")),
          tla.name("e")))

    assert(expected == sugarFree)
  }

  test("chain 3 excepts") {
    // [f EXCEPT ![i][j][k] = e]
    val highCalories =
      tla.except(
        tla.name("f"),
        tla.tuple(tla.name("i"), tla.name("j"), tla.name("k")),
        tla.name("e"))
    val sugarFree = desugarer.transform(highCalories)
    // becomes [ f EXCEPT ![i] = [f[i] EXCEPT ![j] = [f[i][j] EXCEPT ![k] = e] ] ]
    val expected = tla.except(
      tla.name("f"),
      tla.tuple(tla.name("i")),
      tla.except(
        tla.appFun(tla.name("f"), tla.name("i")),
        tla.tuple(tla.name("j")),
        tla.except(
          tla.appFun(
            tla.appFun(tla.name("f"),
              tla.name("i")),
            tla.name("j")),
          tla.tuple(tla.name("k")),
          tla.name("e"))))

    assert(expected == sugarFree)
  }

  test("unfold UNCHANGED <<x, <<y, z>> >> to UNCHANGED <<x, y, z>>") {
    // This is an idiom that was probably introduced by Diego Ongaro in Raft.
    // There is no added value in this construct, so it is just sugar.
    // So, we do the transformation right here.
    val unchanged = tla.unchangedTup(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z")))
    val sugarFree = desugarer.transform(unchanged)
    val expected = tla.unchangedTup(tla.name("x"), tla.name("y"), tla.name("z"))
    assert(expected == sugarFree)
  }

  test("simplify tuples in filters") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    val filter =
      tla.filter(
        tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
        tla.name("XYZ"),
        tla.and(tla.eql(tla.name("x"), tla.int(3)),
                tla.eql(tla.name("y"), tla.int(4))))
    val sugarFree = desugarer.transform(filter)
    val expected =
      tla.filter(
        tla.name("x_y_z"),
        tla.name("XYZ"),
        tla.and(
          tla.eql(tla.appFun(tla.name("x_y_z"), tla.int(1)), tla.int(3)),
          tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)),
                             tla.int(1)),
            tla.int(4))
        ))////
    assert(expected == sugarFree)
  }

  test("simplify tuples in maps") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    val map =
      tla.map(
        tla.plus(tla.name("x"), tla.name("y")),
        tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
        tla.name("XYZ"))
    val sugarFree = desugarer.transform(map)
    val expected =
      tla.map(
        tla.plus(tla.appFun(tla.name("x_y_z"), tla.int(1)),
          tla.appFun(tla.appFun(tla.name("x_y_z"),
                     tla.int(2)),
                     tla.int(1))),
        tla.name("x_y_z"),
        tla.name("XYZ")
        )////
    assert(expected == sugarFree)
  }

  test("simplify tuples in functions") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    val map =
      tla.funDef(
        tla.plus(tla.name("x"), tla.name("y")),
        tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
        tla.name("XYZ"))
    val sugarFree = desugarer.transform(map)
    val expected =
      tla.funDef(
        tla.plus(tla.appFun(tla.name("x_y_z"), tla.int(1)),
          tla.appFun(tla.appFun(tla.name("x_y_z"),
                     tla.int(2)),
                     tla.int(1))),
        tla.name("x_y_z"),
        tla.name("XYZ")
        )////
    assert(expected == sugarFree)
  }
}
