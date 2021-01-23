package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestDesugarer extends FunSuite with BeforeAndAfterEach {
  private var desugarer = new Desugarer(TrackerWithListeners())

  override def beforeEach(): Unit = {
    desugarer = new Desugarer(TrackerWithListeners())
  }

  test("chain 2 excepts") {
    // input: [f EXCEPT ![i][j] = e]
    val highCalories =
      tla.except(tla.name("f"), tla.tuple(tla.name("i"), tla.name("j")), tla.name("e"))
    val sugarFree = desugarer.transform(highCalories)
    // output [ f EXCEPT ![i] = [f[i] EXCEPT ![j] = e] ]
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
    // input: [f EXCEPT ![i][j][k] = e]
    val highCalories =
      tla.except(
        tla.name("f"),
        tla.tuple(tla.name("i"), tla.name("j"), tla.name("k")),
        tla.name("e"))
    val sugarFree = desugarer.transform(highCalories)
    // output: [ f EXCEPT ![i] = [f[i] EXCEPT ![j] = [f[i][j] EXCEPT ![k] = e] ] ]
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

  test("""rewrite UNCHANGED <<x, y>> >> to x' = x /\ y' = y""") {
    // input: <<x, <<y>> >>
    val unchanged = tla.unchangedTup(tla.name("x"), tla.tuple(tla.name("y")))
    val sugarFree = desugarer.transform(unchanged)
    // output: x' = x /\ y' = y
    val expected =
      tla.and(
        tla.eql(tla.prime(tla.name("x")), tla.name("x")),
        tla.eql(tla.prime(tla.name("y")), tla.name("y"))
      ) ///
    assert(expected == sugarFree)
  }

  test("unfold UNCHANGED <<x, <<y, z>> >> to UNCHANGED <<x, y, z>>") {
    // This is an idiom that was probably introduced by Diego Ongaro in Raft.
    // There is no added value in this construct, so it is just sugar.
    // So, we do the transformation right here.
    val unchanged = tla.unchangedTup(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z")))
    val sugarFree = desugarer.transform(unchanged)
    val expected =
      tla.and(
        tla.eql(tla.prime(tla.name("x")), tla.name("x")),
        tla.eql(tla.prime(tla.name("y")), tla.name("y")),
        tla.eql(tla.prime(tla.name("z")), tla.name("z"))
      ) ///
    assert(expected == sugarFree)
  }

  test("simplify tuples in filters") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: { <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val filter =
    tla.filter(
      tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
      tla.name("XYZ"),
      tla.and(tla.eql(tla.name("x"), tla.int(3)),
        tla.eql(tla.name("y"), tla.int(4))))
    val sugarFree = desugarer.transform(filter)
    // output: { x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val expected =
      tla.filter(
        tla.name("x_y_z"),
        tla.name("XYZ"),
        tla.and(
          tla.eql(tla.appFun(tla.name("x_y_z"), tla.int(1)), tla.int(3)),
          tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)),
            tla.int(1)),
            tla.int(4))
        )) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in maps") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: { <<x, <<y, z>> >> \in XYZ |-> x + y }
    val map =
    tla.map(
      tla.plus(tla.name("x"), tla.name("y")),
      tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
      tla.name("XYZ"))
    val sugarFree = desugarer.transform(map)
    // output: { x_y_z \in XYZ: x_y_z[1] + x_y_z[2][1] }
    val expected =
      tla.map(
        tla.plus(tla.appFun(tla.name("x_y_z"), tla.int(1)),
          tla.appFun(tla.appFun(tla.name("x_y_z"),
            tla.int(2)),
            tla.int(1))),
        tla.name("x_y_z"),
        tla.name("XYZ")
      ) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in existentials") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: \E <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val filter =
    tla.exists(
      tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
      tla.name("XYZ"),
      tla.and(tla.eql(tla.name("x"), tla.int(3)),
        tla.eql(tla.name("y"), tla.int(4))))
    val sugarFree = desugarer.transform(filter)
    // output: \E x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val expected =
      tla.exists(
        tla.name("x_y_z"),
        tla.name("XYZ"),
        tla.and(
          tla.eql(tla.appFun(tla.name("x_y_z"), tla.int(1)), tla.int(3)),
          tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)),
            tla.int(1)),
            tla.int(4))
        )) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in universals") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: \A <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val filter =
    tla.forall(
      tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
      tla.name("XYZ"),
      tla.and(tla.eql(tla.name("x"), tla.int(3)),
        tla.eql(tla.name("y"), tla.int(4))))
    val sugarFree = desugarer.transform(filter)
    // output: \A x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val expected =
      tla.forall(
        tla.name("x_y_z"),
        tla.name("XYZ"),
        tla.and(
          tla.eql(tla.appFun(tla.name("x_y_z"), tla.int(1)), tla.int(3)),
          tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)),
            tla.int(1)),
            tla.int(4))
        )) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in functions") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: [<<x, <<y, z>> >> \in XYZ |-> x + y]
    val map =
    tla.funDef(
      tla.plus(tla.name("x"), tla.name("y")),
      tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
      tla.name("XYZ"))
    val sugarFree = desugarer.transform(map)
    // output: [ x_y_z \in XYZ |-> x_y_z[1] + x_y_z[2][1] ]
    val expected =
      tla.funDef(
        tla.plus(tla.appFun(tla.name("x_y_z"), tla.int(1)),
          tla.appFun(tla.appFun(tla.name("x_y_z"),
            tla.int(2)),
            tla.int(1))),
        tla.name("x_y_z"),
        tla.name("XYZ")
      ) ////
    assert(expected == sugarFree)
  }

  test("keep one argument functions") {
    // make sure that a function of a single argument does not get modified, e.g., no tuples added
    // input: [x \in X |-> {x}]
    val fundef =
    tla.funDef(
      tla.enumSet(tla.name("x")),
      tla.name("x"),
      tla.name("X"))
    val sugarFree = desugarer.transform(fundef)
    assert(fundef == sugarFree)
  }

  test("simplify multi-argument functions") {
    // The user may write multi-argument functions, which we collapse into tuples
    // input: [ x \in X, y \in Y |-> x + y ]
    val map =
    tla.funDef(
      tla.plus(tla.name("x"), tla.name("y")),
      tla.name("x"), tla.name("X"),
      tla.name("y"), tla.name("Y"))
    val sugarFree = desugarer.transform(map)
    // output: [ x_y \in X \X Y |-> x_y[1] + x_y[2] ]
    val expected =
      tla.funDef(
        tla.plus(tla.appFun(tla.name("x_y"), tla.int(1)),
          tla.appFun(tla.name("x_y"), tla.int(2))),
        tla.name("x_y"),
        tla.times(tla.name("X"), tla.name("Y"))
      ) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in recursive functions") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: f[x \in S, y \in T] == x + y
    val map =
    tla.recFunDef(
      tla.plus(tla.name("x"), tla.name("y")),
      tla.name("x"), tla.name("S"),
      tla.name("y"), tla.name("T"))
    val sugarFree = desugarer.transform(map)
    // output: f[x_y \in S \X T] == x_y[1] + x_y[2]
    val expected =
      tla.recFunDef(
        tla.plus(tla.appFun(tla.name("x_y"), tla.int(1)),
          tla.appFun(tla.name("x_y"), tla.int(2))),
        tla.name("x_y"),
        tla.times(tla.name("S"), tla.name("T"))
      ) ////
    assert(expected == sugarFree)
  }

  test("keep one argument recursive functions") {
    // make sure that a function of a single argument does not get modified, e.g., no tuples added
    // input: [x \in X |-> {x}]
    val recFun =
      tla.recFunDef(
        tla.enumSet(tla.name("x")),
        tla.name("x"),
        tla.name("X"))
    val sugarFree = desugarer.transform(recFun)
    assert(recFun == sugarFree)
  }
}
