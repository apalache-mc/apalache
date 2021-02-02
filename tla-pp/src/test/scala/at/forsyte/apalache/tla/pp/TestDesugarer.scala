package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.SimpleFormalParam
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
      tla.except(tla.name("f"), tla.tuple(tla.name("i")),
          tla.except(tla.appFun(tla.name("f"), tla.name("i")), tla.tuple(tla.name("j")), tla.name("e")))

    assert(expected == sugarFree)
  }

  test("chain 3 excepts") {
    // input: [f EXCEPT ![i][j][k] = e]
    val highCalories =
      tla.except(tla.name("f"), tla.tuple(tla.name("i"), tla.name("j"), tla.name("k")), tla.name("e"))
    val sugarFree = desugarer.transform(highCalories)
    // output: [ f EXCEPT ![i] = [f[i] EXCEPT ![j] = [f[i][j] EXCEPT ![k] = e] ] ]
    val expected = tla.except(tla.name("f"), tla.tuple(tla.name("i")),
        tla.except(tla.appFun(tla.name("f"), tla.name("i")), tla.tuple(tla.name("j")),
            tla.except(tla.appFun(tla.appFun(tla.name("f"), tla.name("i")), tla.name("j")), tla.tuple(tla.name("k")),
                tla.name("e"))))

    assert(expected == sugarFree)
  }

  test("""rewrite UNCHANGED x to x' = x""") {
    // input: x
    val unchanged = tla.unchanged(tla.name("x"))
    val sugarFree = desugarer.transform(unchanged)
    // output: x' = x
    val expected = tla.eql(tla.prime(tla.name("x")), tla.name("x"))
    assert(expected == sugarFree)
  }

  test("""rewrite UNCHANGED <<x, y>> to x' = x /\ y' = y""") {
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

  test("""rewrite <<x, y>> = <<a, b>> to x = a /\ y = b""") {
    // This pattern looks like a parallel assignment. It stems from preprocessing of UNCHANGED and prime.
    // input: <<x, y>> = <<a, b>>
    val parallel =
      tla.eql(tla.tuple(tla.name("x"), tla.name("y")), tla.tuple(tla.name("a"), tla.name("b")))

    val sugarFree = desugarer.transform(parallel)
    // output: x = a /\ y = b
    val expected =
      tla.and(
          tla.eql(tla.name("x"), tla.name("a")),
          tla.eql(tla.name("y"), tla.name("b"))
      ) ///
    assert(expected == sugarFree)
  }

  test("""rewrite <<x, y>> /= <<a, b>> to x /= a \/ y /= b""") {
    val left = tla.tuple(tla.name("x"), tla.name("y"))
    val right = tla.tuple(tla.name("a"), tla.name("b"))
    // input: <<x, y>> /= <<a, b>>
    val parallel = tla.neql(left, right)

    val sugarFree = desugarer.transform(parallel)
    // output: x /= a \/ y /= b
    val expected =
      tla.or(
          tla.neql(tla.name("x"), tla.name("a")),
          tla.neql(tla.name("y"), tla.name("b"))
      ) ///
    assert(expected == sugarFree)
  }

  test("""rewrite <<x, y>> = <<a, b, c>> to FALSE""") {
    val left = tla.tuple(tla.name("x"), tla.name("y"))
    val right = tla.tuple(tla.name("a"), tla.name("b"), tla.name("c"))
    // input: <<x, y>> = <<a, b, c>>
    val parallel = tla.eql(left, right)

    val sugarFree = desugarer.transform(parallel)
    // output: FALSE
    val expected = tla.bool(false)
    assert(expected == sugarFree)
  }

  test("""rewrite <<x, y>> /= <<a, b, c>> to TRUE""") {
    val left = tla.tuple(tla.name("x"), tla.name("y"))
    val right = tla.tuple(tla.name("a"), tla.name("b"), tla.name("c"))
    // input: <<x, y>> /= <<a, b, c>>
    val parallel = tla.neql(left, right)

    val sugarFree = desugarer.transform(parallel)
    // output: TRUE
    val expected = tla.bool(true)
    assert(expected == sugarFree)
  }

  test("unfold UNCHANGED <<x, <<y, z>> >> to UNCHANGED <<x, y, z>>") {
    // This is an idiom that was probably introduced by Diego Ongaro in Raft.
    // There is no added value in this construct, so it is just sugar.
    // We do the transformation right here.
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

  test("""rewrite UNCHANGED <<>> to TRUE""") {
    // this is a regression for issue #375
    // input: << >>
    val unchanged = tla.unchangedTup()
    val sugarFree = desugarer.transform(unchanged)
    // output: TRUE
    val expected = tla.bool(true)
    assert(expected == sugarFree)
  }

  test("""rewrite UNCHANGED << <<>>, <<>> >> to TRUE""") {
    // this is a regression for issue #375
    // input: << <<>>, <<>> >>
    val unchanged = tla.unchangedTup(tla.unchangedTup(), tla.unchangedTup())
    val sugarFree = desugarer.transform(unchanged)
    // output: TRUE
    val expected = tla.bool(true)
    assert(expected == sugarFree)
  }

  test("""rewrite UNCHANGED f[i] to (f[i])' = f[i]""") {
    // this is a regression for issue #471
    // input: UNCHANGED f[i]
    val app = tla.appFun(tla.name("f"), tla.name("i"))
    val sugarFree = desugarer.transform(tla.unchangedTup(app))
    // output: (f[i])' = f[i]
    val expected = tla.eql(tla.prime(app), app)
    assert(expected == sugarFree)
  }

  test("simplify tuples in filters") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: { <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val filter =
      tla.filter(tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))), tla.name("XYZ"),
          tla.and(tla.eql(tla.name("x"), tla.int(3)), tla.eql(tla.name("y"), tla.int(4))))
    val sugarFree = desugarer.transform(filter)
    // output: { x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val expected =
      tla.filter(tla.name("x_y_z"), tla.name("XYZ"),
          tla.and(
              tla.eql(tla.appFun(tla.name("x_y_z"), tla.int(1)), tla.int(3)),
              tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)), tla.int(1)), tla.int(4))
          )) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in maps") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: { <<x, <<y, z>> >> \in XYZ |-> x + y }
    val map =
      tla.map(tla.plus(tla.name("x"), tla.name("y")), tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))),
          tla.name("XYZ"))
    val sugarFree = desugarer.transform(map)
    // output: { x_y_z \in XYZ: x_y_z[1] + x_y_z[2][1] }
    val expected =
      tla.map(
          tla.plus(tla.appFun(tla.name("x_y_z"), tla.int(1)),
              tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)), tla.int(1))),
          tla.name("x_y_z"),
          tla.name("XYZ")
      ) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in existentials") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: \E <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val filter =
      tla.exists(tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))), tla.name("XYZ"),
          tla.and(tla.eql(tla.name("x"), tla.int(3)), tla.eql(tla.name("y"), tla.int(4))))
    val sugarFree = desugarer.transform(filter)
    // output: \E x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val expected =
      tla.exists(tla.name("x_y_z"), tla.name("XYZ"),
          tla.and(
              tla.eql(tla.appFun(tla.name("x_y_z"), tla.int(1)), tla.int(3)),
              tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)), tla.int(1)), tla.int(4))
          )) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in universals") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: \A <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val filter =
      tla.forall(tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))), tla.name("XYZ"),
          tla.and(tla.eql(tla.name("x"), tla.int(3)), tla.eql(tla.name("y"), tla.int(4))))
    val sugarFree = desugarer.transform(filter)
    // output: \A x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val expected =
      tla.forall(tla.name("x_y_z"), tla.name("XYZ"),
          tla.and(
              tla.eql(tla.appFun(tla.name("x_y_z"), tla.int(1)), tla.int(3)),
              tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)), tla.int(1)), tla.int(4))
          )) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in functions") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: [<<x, <<y, z>> >> \in XYZ |-> x + y]
    val map =
      tla.funDef(tla.plus(tla.name("x"), tla.name("y")),
          tla.tuple(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z"))), tla.name("XYZ"))
    val sugarFree = desugarer.transform(map)
    // output: [ x_y_z \in XYZ |-> x_y_z[1] + x_y_z[2][1] ]
    val expected =
      tla.funDef(
          tla.plus(tla.appFun(tla.name("x_y_z"), tla.int(1)),
              tla.appFun(tla.appFun(tla.name("x_y_z"), tla.int(2)), tla.int(1))),
          tla.name("x_y_z"),
          tla.name("XYZ")
      ) ////
    assert(expected == sugarFree)
  }

  test("keep one argument functions") {
    // make sure that a function of a single argument does not get modified, e.g., no tuples added
    // input: [x \in X |-> {x}]
    val fundef =
      tla.funDef(tla.enumSet(tla.name("x")), tla.name("x"), tla.name("X"))
    val sugarFree = desugarer.transform(fundef)
    assert(fundef == sugarFree)
  }

  test("simplify multi-argument functions") {
    // The user may write multi-argument functions, which we collapse into tuples
    // input: [ x \in X, y \in Y |-> x + y ]
    val map =
      tla.funDef(tla.plus(tla.name("x"), tla.name("y")), tla.name("x"), tla.name("X"), tla.name("y"), tla.name("Y"))
    val sugarFree = desugarer.transform(map)
    // output: [ x_y \in X \X Y |-> x_y[1] + x_y[2] ]
    val expected =
      tla.funDef(
          tla.plus(tla.appFun(tla.name("x_y"), tla.int(1)), tla.appFun(tla.name("x_y"), tla.int(2))),
          tla.name("x_y"),
          tla.times(tla.name("X"), tla.name("Y"))
      ) ////
    assert(expected == sugarFree)
  }

  test("simplify tuples in recursive functions") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: f[x \in S, y \in T] == x + y
    val map =
      tla.recFunDef(tla.plus(tla.name("x"), tla.name("y")), tla.name("x"), tla.name("S"), tla.name("y"), tla.name("T"))
    val sugarFree = desugarer.transform(map)
    // output: f[x_y \in S \X T] == x_y[1] + x_y[2]
    val expected =
      tla.recFunDef(
          tla.plus(tla.appFun(tla.name("x_y"), tla.int(1)), tla.appFun(tla.name("x_y"), tla.int(2))),
          tla.name("x_y"),
          tla.times(tla.name("S"), tla.name("T"))
      ) ////
    assert(expected == sugarFree)
  }

  test("keep one argument recursive functions") {
    // make sure that a function of a single argument does not get modified, e.g., no tuples added
    // input: [x \in X |-> {x}]
    val recFun =
      tla.recFunDef(tla.enumSet(tla.name("x")), tla.name("x"), tla.name("X"))
    val sugarFree = desugarer.transform(recFun)
    assert(recFun == sugarFree)
  }

  test("accept calls to user-defined operators") {
    // Foo(1)
    val app = tla.appOp(tla.name("Foo"), tla.int(1))
    val sugarFree = desugarer(app)
    // do nothing and do not complain
    assert(sugarFree == app)
  }

  test("accept n-ary let-in definitions") {
    // Foo(1)
    val fooDef = tla.declOp("Foo", tla.name("x"), SimpleFormalParam("x"))
    val letIn = tla.letIn(tla.appOp(tla.name("Foo"), tla.int(1)), fooDef)
    val sugarFree = desugarer(letIn)
    // do nothing and do not complain
    assert(sugarFree == letIn)
  }
}
