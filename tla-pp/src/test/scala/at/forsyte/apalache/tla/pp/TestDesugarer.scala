package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.typecheck.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.{SimpleFormalParam, TlaEx}
import at.forsyte.apalache.tla.typecheck.{BoolT1, FunT1, IntT1, OperT1, RecT1, SetT1, StrT1, TlaType1, TupT1}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestDesugarer extends FunSuite with BeforeAndAfterEach {
  private var gen: UniqueNameGenerator = _
  private var desugarer: Desugarer = _
  private val exceptTypes = Map(
      "f1" -> FunT1(IntT1(), IntT1()),
      "f2" -> FunT1(IntT1(), FunT1(IntT1(), IntT1())),
      "f3" -> FunT1(IntT1(), FunT1(IntT1(), FunT1(IntT1(), IntT1()))),
      "O1" -> OperT1(Seq(), FunT1(IntT1(), IntT1())),
      "O2" -> OperT1(Seq(), FunT1(IntT1(), FunT1(IntT1(), IntT1()))),
      "O3" -> OperT1(Seq(), FunT1(IntT1(), FunT1(IntT1(), FunT1(IntT1(), IntT1())))),
      "i" -> TupT1(IntT1()),
      "i1" -> TupT1(IntT1()),
      "i2" -> TupT1(IntT1(), IntT1()),
      "i3" -> TupT1(IntT1(), IntT1(), IntT1())
  )
  private val unchangedTypes = Map(
      "i" -> IntT1(),
      "b" -> BoolT1(),
      "et" -> TupT1(),
      "b1" -> TupT1(BoolT1()),
      "i_b1_2" -> TupT1(IntT1(), TupT1(BoolT1())),
      "ib_2" -> TupT1(IntT1(), BoolT1()),
      "ibi_3" -> TupT1(IntT1(), BoolT1()),
      "i_ib_2_2" -> TupT1(IntT1(), TupT1(IntT1(), BoolT1())),
      "f1" -> FunT1(IntT1(), IntT1())
  )
  private val tupleTypes = Map(
      "b" -> BoolT1(),
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "i_to_I" -> FunT1(IntT1(), SetT1(IntT1())),
      "ii_to_i" -> FunT1(TupT1(IntT1(), IntT1()), IntT1()),
      "ii_2" -> TupT1(IntT1(), IntT1()),
      "i_ii_2_2" -> TupT1(IntT1(), TupT1(IntT1(), IntT1())),
      "I_II_2_2" -> SetT1(TupT1(IntT1(), TupT1(IntT1(), IntT1()))),
      "II_2" -> SetT1(TupT1(IntT1(), IntT1())),
      "i_ii_2_2_to_ii_2" -> FunT1(TupT1(IntT1(), TupT1(IntT1(), IntT1())), TupT1(IntT1(), IntT1()))
  )

  override def beforeEach(): Unit = {
    gen = new UniqueNameGenerator()
    desugarer = new Desugarer(gen, new IdleTracker())
  }

  // call the operator that returns a function of type stored in exceptTypes(funAlias) and access it with indices
  private def callAndAccess(operName: String, funAlias: String, indices: String*): TlaEx = {
    def eatFun(tt: TlaType1, key: String): (TlaType1, TlaType1) = {
      tt match {
        case FunT1(arg, res) =>
          (arg, res)

        case RecT1(fieldTypes) =>
          if (fieldTypes.contains(key)) {
            (StrT1(), fieldTypes(key))
          } else {
            throw new IllegalArgumentException(s"No key $key in $tt")
          }

        case TupT1(elems @ _*) =>
          val intKey = key.toInt
          if (intKey > 0 && intKey <= elems.length) {
            (IntT1(), elems(intKey))
          } else {
            throw new IllegalArgumentException(s"No index $key in $tt")
          }
      }
    }

    val tt = exceptTypes(funAlias)
    val operT = OperT1(Seq(), tt)
    indices.foldLeft(tla.appOp(tla.name(operName).typed(operT)).typed(tt)) { case (a, n) =>
      val (argT, resT) = eatFun(a.typeTag.asTlaType1(), n)
      tla.appFun(a, tla.name(n).typed(argT)).typed(resT)
    }
  }

  test("EXCEPT one-dimensional, one index") {
    // input: [f EXCEPT ![i] = e]
    val input =
      tla
        .except(tla.name("f") ? "f1", tla.tuple(tla.name("i") ? "i") ? "i1", tla.name("e") ? "i")
        .typed(exceptTypes, "f1")
    // output: the same as input
    val output = desugarer.transform(input)
    assert(output eqTyped input)
  }

  test("EXCEPT two-dimensional, one index") {
    // input: [f EXCEPT ![i][j] = e]
    val input =
      tla
        .except(tla.name("f") ? "f2", tla.tuple(tla.name("i") ? "i", tla.name("j") ? "i") ? "i2", tla.name("e") ? "i")
        .typed(exceptTypes, "f2")
    val output = desugarer.transform(input)
    // output: series of LET-IN definitions
    // LET t_1 == f
    //     t_2 == [t_1()[i] EXCEPT ![j] = e]
    //     t_3 == [t_1() EXCEPT ![i] = t_2()]
    //     IN t_3()
    val defs = Seq(
        tla
          .declOp("t_1", tla.name("f") ? "f2")
          .typedOperDecl(exceptTypes, "O2"),
        tla
          .declOp("t_2", tla.except(callAndAccess("t_1", "f2", "i"), tla.name("j") ? "i", tla.name("e") ? "i") ? "f1")
          .typedOperDecl(exceptTypes, "O1"),
        tla
          .declOp("t_3", tla.except(callAndAccess("t_1", "f1"), tla.name("i") ? "i", callAndAccess("t_2", "f1")) ? "f2")
          .typedOperDecl(exceptTypes, "O2")
    )

    val expected: TlaEx =
      tla
        .letIn(callAndAccess("t_3", "f2"), defs: _*)
        .typed(exceptTypes, "f2")

    assert(expected eqTyped output)
  }

  test("EXCEPT three-dimensional, one index") {
    // input: [f EXCEPT ![i][j][k] = e]
    val input =
      tla
        .except(tla.name("f") ? "f3", tla.tuple(tla.name("i") ? "i", tla.name("j") ? "i", tla.name("k") ? "i") ? "i3",
            tla.name("e") ? "i")
        .typed(exceptTypes, "f3")
    val output = desugarer.transform(input)
    // output: series of LET-IN definitions
    // LET t_1 == f
    //     t_2 == [t_1()[i][j] EXCEPT ![k] = e]
    //     t_3 == [t_1()[i] EXCEPT ![j] = t_2()]
    //     t_4 == [t_1() EXCEPT ![i] = t_3()]
    //     IN t_4()
    val defs = Seq(
        tla
          .declOp("t_1", tla.name("f") ? "f3")
          .typedOperDecl(exceptTypes, "O3"),
        tla
          .declOp("t_2",
              tla.except(callAndAccess("t_1", "f3", "i", "j"), tla.name("k") ? "i", tla.name("e") ? "i") ? "f1")
          .typedOperDecl(exceptTypes, "O1"),
        tla
          .declOp("t_3",
              tla.except(callAndAccess("t_1", "f3", "i"), tla.name("j") ? "i", callAndAccess("t_2", "f1")) ? "f2")
          .typedOperDecl(exceptTypes, "O2"),
        tla
          .declOp("t_4", tla.except(callAndAccess("t_1", "f1"), tla.name("i") ? "i", callAndAccess("t_3", "f3")) ? "f3")
          .typedOperDecl(exceptTypes, "O3")
    )

    val expected: TlaEx =
      tla
        .letIn(callAndAccess("t_4", "f3"), defs: _*)
        .typed(exceptTypes, "f3")

    assert(expected eqTyped output)
  }

  test("EXCEPT with two updates") {
    // input: [f EXCEPT ![i][j] = e1, ![k][l] = e2]
    val input =
      tla
        .except(tla.name("f") ? "f2", tla.tuple(tla.name("i") ? "i", tla.name("j") ? "i") ? "i2", tla.name("e1") ? "i",
            tla.tuple(tla.name("k") ? "i", tla.name("l") ? "i") ? "i2", tla.name("e2") ? "i")
        .typed(exceptTypes, "f2")
    val output = desugarer.transform(input)
    // output: a series of definitions
    // LET t_1 == f
    //     t_2 == [t_1()[i] EXCEPT ![j] = e1]
    //     t_3 == [t_1() EXCEPT ![i] = t_2()]
    //     t_4 == [t_3()[k] EXCEPT ![l] = e2]
    //     t_5 == [t_3() EXCEPT ![k] = t_4()]
    //     IN t_5()
    val defs = Seq(
        tla
          .declOp("t_1", tla.name("f") ? "f2")
          .typedOperDecl(exceptTypes, "O2"),
        tla
          .declOp("t_2", tla.except(callAndAccess("t_1", "f2", "i"), tla.name("j") ? "i", tla.name("e1") ? "i") ? "f1")
          .typedOperDecl(exceptTypes, "O1"),
        tla.declOp("t_3",
            tla.except(callAndAccess("t_1", "f2"), tla.name("i") ? "i", callAndAccess("t_2", "f1")) ? "f2")
          typedOperDecl (exceptTypes, "O2"),
        tla
          .declOp("t_4", tla.except(callAndAccess("t_3", "f2", "k"), tla.name("l") ? "i", tla.name("e2") ? "i") ? "f1")
          .typedOperDecl(exceptTypes, "O1"),
        tla
          .declOp("t_5", tla.except(callAndAccess("t_3", "f2"), tla.name("k") ? "i", callAndAccess("t_4", "f1")) ? "f2")
          .typedOperDecl(exceptTypes, "O2")
    )

    val expected: TlaEx =
      tla
        .letIn(callAndAccess("t_5", "f2"), defs: _*)
        .typed(exceptTypes, "f2")

    assert(expected eqTyped output)
  }

  test("""rewrite UNCHANGED x to x' = x""") {
    // input: x
    val input = tla
      .unchanged(tla.name("x") ? "i")
      .typed(unchangedTypes, "b")
    val output = desugarer.transform(input)
    // output: x' = x
    val expected =
      tla
        .eql(tla.prime(tla.name("x") ? "i") ? "i", tla.name("x") ? "i")
        .typed(unchangedTypes, "b")
    assert(expected eqTyped output)
  }

  test("""rewrite UNCHANGED <<x, <<y>> >> to x' = x /\ y' = y""") {
    // input: <<x, <<y>> >>
    val input =
      tla
        .unchanged(tla.tuple(tla.name("x") ? "i", tla.tuple(tla.name("y") ? "b") ? "b1") ? "i_b1_2")
        .typed(unchangedTypes, "b")
    val output = desugarer.transform(input)
    // output: x' = x /\ y' = y
    val expected: TlaEx =
      tla
        .and(
            tla.eql(tla.prime(tla.name("x") ? "i") ? "i", tla.name("x") ? "i") ? "b",
            tla.eql(tla.prime(tla.name("y") ? "b") ? "b", tla.name("y") ? "b") ? "b"
        )
        .typed(unchangedTypes, "b")
    assert(expected eqTyped output)
  }

  test("""rewrite <<x, y>> = <<a, b>> to x = a /\ y = b""") {
    // This pattern looks like a parallel assignment. It stems from preprocessing of UNCHANGED and prime.
    // input: <<x, y>> = <<a, b>>
    val input =
      tla
        .eql(tla.tuple(tla.name("x") ? "i", tla.name("y") ? "b") ? "ib_2",
            tla.tuple(tla.name("a") ? "i", tla.name("b") ? "b") ? "ib_2")
        .typed(unchangedTypes, "b")

    val output = desugarer.transform(input)
    // output: x = a /\ y = b
    val expected: TlaEx =
      tla
        .and(
            tla.eql(tla.name("x") ? "i", tla.name("a") ? "b") ? "b",
            tla.eql(tla.name("y") ? "i", tla.name("b") ? "b") ? "b"
        )
        .typed(unchangedTypes, "b")
    assert(expected eqTyped output)
  }

  test("""rewrite <<x, y>> /= <<a, b>> to x /= a \/ y /= b""") {
    val left = tla.tuple(tla.name("x") ? "i", tla.name("y") ? "b") ? "ib_2"
    val right = tla.tuple(tla.name("a") ? "i", tla.name("b") ? "b") ? "ib_2"
    // input: <<x, y>> /= <<a, b>>
    val parallel = tla.neql(left, right).typed(unchangedTypes, "b")

    val output = desugarer.transform(parallel)
    // output: x /= a \/ y /= b
    val expected =
      tla
        .or(
            tla.neql(tla.name("x") ? "i", tla.name("a") ? "b") ? "b",
            tla.neql(tla.name("y") ? "i", tla.name("b") ? "b") ? "b"
        )
        .typed(unchangedTypes, "b")
    assert(expected eqTyped output)
  }

  test("""rewrite <<x, y>> = <<a, b, c>> to FALSE""") {
    val left = tla.tuple(tla.name("x") ? "i", tla.name("y") ? "b") ? "ib_2"
    val right = tla.tuple(tla.name("a") ? "i", tla.name("b") ? "b", tla.name("c") ? "i") ? "ibi_3"
    // input: <<x, y>> = <<a, b, c>>
    val input = tla.eql(left, right).typed(unchangedTypes, "b")

    val output = desugarer.transform(input)
    // output: FALSE
    val expected: TlaEx = tla.bool(false).typed()
    assert(expected eqTyped output)
  }

  test("""rewrite <<x, y>> /= <<a, b, c>> to TRUE""") {
    val left = tla.tuple(tla.name("x") ? "i", tla.name("y") ? "b") ? "ib_2"
    val right = tla.tuple(tla.name("a") ? "i", tla.name("b") ? "b", tla.name("c") ? "i") ? "ibi_3"
    // input: <<x, y>> /= <<a, b, c>>
    val parallel = tla.neql(left, right).typed(unchangedTypes, "b")

    val output = desugarer.transform(parallel)
    // output: TRUE
    val expected: TlaEx = tla.bool(true).typed()
    assert(expected eqTyped output)
  }

  test("unfold UNCHANGED <<x, <<y, z>> >> to UNCHANGED <<x, y, z>>") {
    // This is an idiom that was probably introduced by Diego Ongaro in Raft.
    // There is no added value in this construct, so it is just sugar.
    // We do the transformation right here.
    val unchanged =
      tla
        .unchanged(tla.tuple(tla.name("x") ? "i",
                tla.tuple(tla.name("y") ? "i", tla.name("z") ? "b") ? "ib_2") ? "i_ib_2_2")
        .typed(unchangedTypes, "b")
    val sugarFree = desugarer.transform(unchanged)
    val expected: TlaEx =
      tla
        .and(
            tla.eql(tla.prime(tla.name("x") ? "i") ? "i", tla.name("x") ? "i") ? "b",
            tla.eql(tla.prime(tla.name("y") ? "i") ? "i", tla.name("y") ? "i") ? "b",
            tla.eql(tla.prime(tla.name("z") ? "i") ? "i", tla.name("z") ? "i") ? "b"
        )
        .typed(unchangedTypes, "b")
    assert(expected eqTyped sugarFree)
  }

  test("""rewrite UNCHANGED <<>> to TRUE""") {
    // this is a regression for issue #375
    // input: << >>
    val input = tla.unchanged(tla.tuple() ? "et").typed(unchangedTypes, "b")
    val output = desugarer.transform(input)
    // output: TRUE
    val expected: TlaEx = tla.bool(true).typed()
    assert(expected eqTyped output)
  }

  test("""rewrite UNCHANGED << <<>>, <<>> >> to TRUE""") {
    // this is a regression for issue #375
    // input: << <<>>, <<>> >>
    val input = tla
      .unchanged(tla.tuple(tla.tuple() ? "et", tla.tuple() ? "et") ? "et_2")
      .typed(unchangedTypes + ("et_2" -> TupT1(TupT1(), TupT1())), "b")
    val output = desugarer.transform(input)
    // output: TRUE
    val expected: TlaEx = tla.bool(true).typed()
    assert(expected eqTyped output)
  }

  test("""rewrite UNCHANGED f[i] to (f[i])' = f[i]""") {
    // this is a regression for issue #471
    // input: UNCHANGED f[i]
    val input = tla
      .unchanged(tla.appFun(tla.name("f") ? "f1", tla.name("i") ? "i") ? "i")
      .typed(unchangedTypes, "b")
    val output = desugarer.transform(input)
    // output: (f[i])' = f[i]
    val expected: TlaEx =
      tla
        .eql(tla.prime(input) ? "b", input)
        .typed(unchangedTypes, "b")
    assert(expected eqTyped output)
  }

  test("simplify tuples in filters") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: { <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val input =
      tla
        .filter(tla.tuple(tla.name("x") ? "i",
                tla.tuple(tla.name("y") ? "i", tla.name("z") ? "i") ? "ii_2") ? "i_ii_2_2",
            tla.name("XYZ") ? "I_II_2_2",
            tla.and(tla.eql(tla.name("x") ? "i", tla.int(3)) ? "b",
                tla.eql(tla.name("y") ? "i", tla.int(4)) ? "b") ? "b")
        .typed(tupleTypes, "I_II_2_2")
    val sugarFree = desugarer.transform(input)
    // output: { x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val output =
      tla
        .filter(tla.name("x_y_z") ? "i_ii_2_2", tla.name("XYZ") ? "I_II_2_2",
            tla.and(
                tla.eql(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(1)) ? "i", tla.int(3) ? "i") ? "b",
                tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(2)) ? "i", tla.int(1)) ? "i",
                    tla.int(4)) ? "b"
            ) ? "b")
        .typed(tupleTypes, "I_II_2_2")
    assert(output eqTyped sugarFree)
  }

  test("simplify tuples in maps") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: { <<x, <<y, z>> >> \in XYZ |-> x + y }
    val map =
      tla
        .map(tla.plus(tla.name("x") ? "i", tla.name("y") ? "i") ? "i",
            tla.tuple(tla.name("x") ? "i", tla.tuple(tla.name("y") ? "i", tla.name("z") ? "i") ? "ii_2") ? "i_ii_2_2",
            tla.name("XYZ") ? "I_II_2_2")
        .typed(tupleTypes, "II_2")
    val output = desugarer.transform(map)
    // output: { x_y_z \in XYZ: x_y_z[1] + x_y_z[2][1] }
    val expected =
      tla
        .map(
            tla.plus(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(1)) ? "i",
                tla.appFun(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(2)) ? "ii_2", tla.int(1)) ? "i") ? "i",
            tla.name("x_y_z") ? "i_ii_2_2",
            tla.name("XYZ") ? "I_II_2_2"
        )
        .typed(tupleTypes, "II_2")
    assert(expected eqTyped output)
  }

  test("simplify tuples in existentials") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: \E <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val input =
      tla
        .exists(tla.tuple(tla.name("x") ? "i",
                tla.tuple(tla.name("y") ? "i", tla.name("z") ? "i") ? "ii_2") ? "i_ii_2_2",
            tla.name("XYZ") ? "I_II_2_2",
            tla.and(tla.eql(tla.name("x") ? "i", tla.int(3)) ? "b",
                tla.eql(tla.name("y") ? "i", tla.int(4)) ? "b") ? "b")
        .typed(tupleTypes, "b")
    val sugarFree = desugarer.transform(input)
    // output: \E x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val output =
      tla
        .exists(tla.name("x_y_z") ? "i_ii_2_2", tla.name("XYZ") ? "I_II_2_2",
            tla.and(
                tla.eql(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(1)) ? "i", tla.int(3)) ? "b",
                tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(2)) ? "i", tla.int(1)) ? "i",
                    tla.int(4)) ? "b"
            ) ? "b")
        .typed(tupleTypes, "b")
    assert(output eqTyped sugarFree)
  }

  test("simplify tuples in universals") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: \A <<x, <<y, z>> >> \in XYZ: x = 3 /\ y = 4 }
    val input =
      tla
        .forall(tla.tuple(tla.name("x") ? "i",
                tla.tuple(tla.name("y") ? "i", tla.name("z") ? "i") ? "ii_2") ? "i_ii_2_2",
            tla.name("XYZ") ? "I_II_2_2",
            tla.and(tla.eql(tla.name("x") ? "i", tla.int(3)) ? "b",
                tla.eql(tla.name("y") ? "i", tla.int(4)) ? "b") ? "b")
        .typed(tupleTypes, "b")
    val sugarFree = desugarer.transform(input)
    // output: \A x_y_z \in XYZ: x_y_z[1] = 3 /\ x_y_z[2][1] = 4 }
    val output =
      tla
        .forall(tla.name("x_y_z") ? "i_ii_2_2", tla.name("XYZ") ? "I_II_2_2",
            tla.and(
                tla.eql(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(1)) ? "i", tla.int(3)) ? "b",
                tla.eql(tla.appFun(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(2)) ? "i", tla.int(1)) ? "i",
                    tla.int(4)) ? "b"
            ) ? "b")
        .typed(tupleTypes, "b")
    assert(output eqTyped sugarFree)
  }

  test("simplify tuples in functions") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: [<<x, <<y, z>> >> \in XYZ |-> x + y]
    val input =
      tla
        .funDef(tla.plus(tla.name("x") ? "i", tla.name("y") ? "i") ? "i",
            tla.tuple(tla.name("x") ? "i", tla.tuple(tla.name("y") ? "i", tla.name("z") ? "i") ? "ii_2") ? "i_ii_2_2",
            tla.name("XYZ") ? "I_II_2_2")
        .typed(tupleTypes, "i_ii_2_2_to_ii_2")
    val output = desugarer.transform(input)
    // output: { x_y_z \in XYZ: x_y_z[1] + x_y_z[2][1] }
    val expected =
      tla
        .funDef(
            tla.plus(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(1)) ? "i",
                tla.appFun(tla.appFun(tla.name("x_y_z") ? "i_ii_2_2", tla.int(2)) ? "ii_2", tla.int(1)) ? "i") ? "i",
            tla.name("x_y_z") ? "i_ii_2_2",
            tla.name("XYZ") ? "I_II_2_2"
        )
        .typed(tupleTypes, "i_ii_2_2_to_ii_2")

    assert(expected eqTyped output)
  }

  test("keep one argument functions") {
    // make sure that a function of a single argument does not get modified, e.g., no tuples added
    // input: [x \in X |-> {x}]
    val input =
      tla
        .funDef(tla.enumSet(tla.name("x") ? "i") ? "I", tla.name("x") ? "i", tla.name("X") ? "I")
        .typed(tupleTypes, "i_to_I")
    val output = desugarer.transform(input)
    assert(input eqTyped output)
  }

  test("simplify multi-argument functions") {
    // The user may write multi-argument functions, which we collapse into tuples
    // input: [ x \in X, y \in Y |-> x + y ]
    val map =
      tla
        .funDef(tla.plus(tla.name("x") ? "i", tla.name("y") ? "i") ? "i", tla.name("x") ? "i", tla.name("X") ? "I",
            tla.name("y") ? "i", tla.name("Y") ? "I")
        .typed(tupleTypes, "ii_to_i")
    val sugarFree = desugarer.transform(map)
    // output: [ x_y \in X \X Y |-> x_y[1] + x_y[2] ]
    val expected: TlaEx =
      tla
        .funDef(
            tla.plus(tla.appFun(tla.name("x_y") ? "ii_2", tla.int(1)) ? "i",
                tla.appFun(tla.name("x_y") ? "ii_2", tla.int(2)) ? "i") ? "i",
            tla.name("x_y") ? "ii_2",
            tla.times(tla.name("X") ? "I", tla.name("Y") ? "I") ? "II_2"
        )
        .typed(tupleTypes, "ii_to_i")
    assert(expected eqTyped sugarFree)
  }

  test("simplify tuples in recursive functions") {
    // TLA+ allows the user to write tuples in expanded form. We introduce tuples instead.
    // input: f[x \in S, y \in T] == x + y
    val input =
      tla
        .recFunDef(tla.plus(tla.name("x") ? "i", tla.name("y") ? "i") ? "i", tla.name("x") ? "i", tla.name("S") ? "I",
            tla.name("y") ? "i", tla.name("T") ? "I")
        .typed(tupleTypes, "ii_to_i")
    val output = desugarer.transform(input)
    // output: f[x_y \in S \X T] == x_y[1] + x_y[2]
    val expected: TlaEx =
      tla
        .recFunDef(
            tla.plus(tla.appFun(tla.name("x_y") ? "ii_2", tla.int(1)) ? "i",
                tla.appFun(tla.name("x_y") ? "ii_2", tla.int(2)) ? "i") ? "i",
            tla.name("x_y") ? "ii_2",
            tla.times(tla.name("S") ? "I", tla.name("T") ? "I") ? "II_2"
        )
        .typed(tupleTypes, "ii_to_i")
    assert(expected eqTyped output)
  }

  test("keep one argument recursive functions") {
    // make sure that a function of a single argument does not get modified, e.g., no tuples added
    // input: [x \in X |-> {x}]
    val input: TlaEx =
      tla
        .recFunDef(tla.enumSet(tla.name("x") ? "i") ? "I", tla.name("x") ? "i", tla.name("X") ? "I")
        .typed(tupleTypes, "i_to_I")
    val output = desugarer.transform(input)
    assert(input eqTyped output)
  }

  test("accept calls to user-defined operators") {
    val types = Map("i" -> IntT1(), "F" -> OperT1(Seq(), IntT1()))
    // Foo(1)
    val input =
      tla
        .appOp(tla.name("Foo") ? "F", tla.int(1) ? "i")
        .typed(types, "i")
    val output = desugarer(input)
    // do nothing and do not complain
    assert(output eqTyped input)
  }

  test("accept n-ary let-in definitions") {
    val types = Map("i" -> IntT1(), "F" -> OperT1(Seq(), IntT1()))
    // Foo(1)
    val fooDef = tla
      .declOp("Foo", tla.name("x") ? "i", SimpleFormalParam("x"))
      .typedOperDecl(types, "F")
    val input = tla
      .letIn(tla.appOp(tla.name("Foo") ? "F", tla.int(1) ? "i") ? "i", fooDef)
      .typed(types, "i")
    val output = desugarer(input)
    // do nothing and do not complain
    assert(output == input)
  }
}
