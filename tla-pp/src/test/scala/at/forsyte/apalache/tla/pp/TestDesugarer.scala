package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.{SimpleFormalParam, TlaEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestDesugarer extends FunSuite with BeforeAndAfterEach {
  private var gen: UniqueNameGenerator = _
  private var desugarer: Desugarer = _

  private def callAndAccess(operName: String, index: String*): TlaEx = {
    index.foldLeft(tla.appOp(tla.name(operName).untyped())) { case (a, n) => tla.appFun(a, tla.name(n)).untyped() }
  }

  override def beforeEach(): Unit = {
    gen = new UniqueNameGenerator()
    desugarer = new Desugarer(gen, new IdleTracker())
  }

  test("EXCEPT one-dimensional, one index") {
    // input: [f EXCEPT ![i] = e]
    val input =
      tla.except(tla.name("f"), tla.tuple(tla.name("i")), tla.name("e")).untyped()
    // output: the same as input
    val output = desugarer.transform(input)
    assert(output == input)
  }

  test("EXCEPT two-dimensional, one index") {
    // input: [f EXCEPT ![i][j] = e]
    val input =
      tla.except(tla.name("f"), tla.tuple(tla.name("i"), tla.name("j")), tla.name("e"))
    val output = desugarer.transform(input)
    // output: series of LET-IN definitions
    // LET t_1 == f
    //     t_2 == [t_1()[i] EXCEPT ![j] = e]
    //     t_3 == [t_1() EXCEPT ![i] = t_2()]
    //     IN t_3()
    val defs = Seq(
        tla.declOp("t_1", tla.name("f")).untypedOperDecl(),
        tla.declOp("t_2", tla.except(callAndAccess("t_1", "i"), tla.name("j"), tla.name("e"))).untypedOperDecl(),
        tla.declOp("t_3", tla.except(callAndAccess("t_1"), tla.name("i"), callAndAccess("t_2"))).untypedOperDecl()
    )

    val expected: TlaEx =
      tla.letIn(callAndAccess("t_3"), defs: _*)

    assert(expected == output)
  }

  test("EXCEPT three-dimensional, one index") {
    // input: [f EXCEPT ![i][j][k] = e]
    val input =
      tla.except(tla.name("f"), tla.tuple(tla.name("i"), tla.name("j"), tla.name("k")), tla.name("e"))
    val output = desugarer.transform(input)
    // output: series of LET-IN definitions
    // LET t_1 == f
    //     t_2 == [t_1()[i][j] EXCEPT ![k] = e]
    //     t_3 == [t_1()[i] EXCEPT ![j] = t_2()]
    //     t_4 == [t_1() EXCEPT ![i] = t_3()]
    //     IN t_4()
    val defs = Seq(
        tla.declOp("t_1", tla.name("f")).untypedOperDecl(),
        tla.declOp("t_2", tla.except(callAndAccess("t_1", "i", "j"), tla.name("k"), tla.name("e"))).untypedOperDecl(),
        tla.declOp("t_3", tla.except(callAndAccess("t_1", "i"), tla.name("j"), callAndAccess("t_2"))).untypedOperDecl(),
        tla.declOp("t_4", tla.except(callAndAccess("t_1"), tla.name("i"), callAndAccess("t_3"))).untypedOperDecl()
    )

    val expected: TlaEx =
      tla.letIn(callAndAccess("t_4"), defs: _*)

    assert(expected == output)
  }

  test("EXCEPT with two updates") {
    // input: [f EXCEPT ![i][j] = e1, ![k][l] = e2]
    val input =
      tla.except(tla.name("f"), tla.tuple(tla.name("i"), tla.name("j")), tla.name("e1"),
          tla.tuple(tla.name("k"), tla.name("l")), tla.name("e2"))
    val output = desugarer.transform(input)
    // output: a series of definitions
    // LET t_1 == f
    //     t_2 == [t_1()[i] EXCEPT ![j] = e1]
    //     t_3 == [t_1() EXCEPT ![i] = t_2()]
    //     t_4 == [t_3()[k] EXCEPT ![l] = e2]
    //     t_5 == [t_3() EXCEPT ![k] = t_4()]
    //     IN t_5()
    val defs = Seq(
        tla.declOp("t_1", tla.name("f")).untypedOperDecl(),
        tla.declOp("t_2", tla.except(callAndAccess("t_1", "i"), tla.name("j"), tla.name("e1"))).untypedOperDecl(),
        tla.declOp("t_3", tla.except(callAndAccess("t_1"), tla.name("i"), callAndAccess("t_2"))).untypedOperDecl(),
        tla.declOp("t_4", tla.except(callAndAccess("t_3", "k"), tla.name("l"), tla.name("e2"))).untypedOperDecl(),
        tla.declOp("t_5", tla.except(callAndAccess("t_3"), tla.name("k"), callAndAccess("t_4"))).untypedOperDecl()
    )

    val expected: TlaEx =
      tla.letIn(callAndAccess("t_5"), defs: _*)

    assert(expected == output)
  }

  test("""rewrite UNCHANGED x to x' = x""") {
    // input: x
    val unchanged = tla.unchanged(tla.name("x"))
    val sugarFree = desugarer.transform(unchanged)
    // output: x' = x
    val expected: TlaEx = tla.eql(tla.prime(tla.name("x")), tla.name("x"))
    assert(expected == sugarFree)
  }

  test("""rewrite UNCHANGED <<x, y>> to x' = x /\ y' = y""") {
    // input: <<x, <<y>> >>
    val unchanged = tla.unchangedTup(tla.name("x"), tla.tuple(tla.name("y")))
    val sugarFree = desugarer.transform(unchanged)
    // output: x' = x /\ y' = y
    val expected: TlaEx =
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
    val expected: TlaEx =
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
    val expected: TlaEx =
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
    val expected: TlaEx = tla.bool(false)
    assert(expected == sugarFree)
  }

  test("""rewrite <<x, y>> /= <<a, b, c>> to TRUE""") {
    val left = tla.tuple(tla.name("x"), tla.name("y"))
    val right = tla.tuple(tla.name("a"), tla.name("b"), tla.name("c"))
    // input: <<x, y>> /= <<a, b, c>>
    val parallel = tla.neql(left, right)

    val sugarFree = desugarer.transform(parallel)
    // output: TRUE
    val expected: TlaEx = tla.bool(true)
    assert(expected == sugarFree)
  }

  test("unfold UNCHANGED <<x, <<y, z>> >> to UNCHANGED <<x, y, z>>") {
    // This is an idiom that was probably introduced by Diego Ongaro in Raft.
    // There is no added value in this construct, so it is just sugar.
    // We do the transformation right here.
    val unchanged = tla.unchangedTup(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z")))
    val sugarFree = desugarer.transform(unchanged)
    val expected: TlaEx =
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
    val expected: TlaEx = tla.bool(true)
    assert(expected == sugarFree)
  }

  test("""rewrite UNCHANGED << <<>>, <<>> >> to TRUE""") {
    // this is a regression for issue #375
    // input: << <<>>, <<>> >>
    val unchanged = tla.unchangedTup(tla.unchangedTup(), tla.unchangedTup())
    val sugarFree = desugarer.transform(unchanged)
    // output: TRUE
    val expected: TlaEx = tla.bool(true)
    assert(expected == sugarFree)
  }

  test("""rewrite UNCHANGED f[i] to (f[i])' = f[i]""") {
    // this is a regression for issue #471
    // input: UNCHANGED f[i]
    val app = tla.appFun(tla.name("f"), tla.name("i"))
    val sugarFree = desugarer.transform(tla.unchangedTup(app))
    // output: (f[i])' = f[i]
    val expected: TlaEx = tla.eql(tla.prime(app), app)
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
    val expected: TlaEx =
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
    val expected: TlaEx =
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
    val expected: TlaEx =
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
    val expected: TlaEx =
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
    val expected: TlaEx =
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
    val fundef: TlaEx =
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
    val expected: TlaEx =
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
    val expected: TlaEx =
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
    val recFun: TlaEx =
      tla.recFunDef(tla.enumSet(tla.name("x")), tla.name("x"), tla.name("X"))
    val sugarFree = desugarer.transform(recFun)
    assert(recFun == sugarFree)
  }

  test("accept calls to user-defined operators") {
    // Foo(1)
    val app: TlaEx = tla.appOp(tla.name("Foo"), tla.int(1))
    val sugarFree = desugarer(app)
    // do nothing and do not complain
    assert(sugarFree == app)
  }

  test("accept n-ary let-in definitions") {
    // Foo(1)
    val fooDef = tla.declOp("Foo", tla.name("x"), SimpleFormalParam("x")).untypedOperDecl()
    val letIn: TlaEx = tla.letIn(tla.appOp(tla.name("Foo"), tla.int(1)), fooDef)
    val sugarFree = desugarer(letIn)
    // do nothing and do not complain
    assert(sugarFree == letIn)
  }
}
