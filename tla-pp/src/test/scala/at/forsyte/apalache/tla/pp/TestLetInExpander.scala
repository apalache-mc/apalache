package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestLetInExpander extends FunSuite {

  import tla._

  private val parser = DefaultType1Parser

  val types =
    Map("i" -> parser("Int"), "b" -> parser("Bool"), "U" -> parser("() => Int"), "C" -> parser("Int => Int"),
        "iTOi" -> parser("Int => Int"), "iTOb" -> parser("Int => Bool"), "iiTOi" -> parser("(Int, Int) => Int"),
        "iiTOb" -> parser("(Int, Int) => Bool"), "si" -> parser("Seq(Int)"))

  private def test1(keepNullary: Boolean): Unit = {
    val n_x = tla.name("x").typed(IntT1())
    val input: TlaEx = n_x
    val output = new LetInExpander(new IdleTracker(), keepNullary = keepNullary)(input)
    val expected = n_x
    assert(expected == output)
    assert(output.eqTyped(expected))
  }

  test("Test 1a: LetInExpander, keepNullary = false") {
    test1(false)
  }

  test("Test 1b: LetInExpander, keepNullary = true") {
    test1(true)
  }

  test("Test 2a: LetInExpander, keepNullary = false") {
    val n_x = tla.name("x").typed(IntT1())
    val n_A = tla.name("A").typed(types, "U")
    val input = letIn(appOp(n_A) ? "i", declOp("A", n_x).typedOperDecl(types, "U")).typed(types, "i")
    val output = new LetInExpander(new IdleTracker(), keepNullary = false)(input)
    val expected = n_x
    assert(expected == output)
    assert(output.eqTyped(expected))
  }

  test("Test 2b: LetInExpander, keepNullary = true") {
    val n_x = tla.name("x").typed(IntT1())
    val n_A = tla.name("A").typed(types, "U")
    val input = letIn(appOp(n_A) ? "i", declOp("A", n_x).typedOperDecl(types, "U")).typed(types, "i")
    val output = new LetInExpander(new IdleTracker(), keepNullary = true)(input)
    val expected = input
    assert(expected == output)
    assert(output.eqTyped(expected))
  }

  private def test3(keepNullary: Boolean): Unit = {
    val n_x = tla.name("x").typed(IntT1())
    val n_y = tla.name("y").typed(IntT1())
    val n_B = tla.name("B").typed(types, "iTOi")
    val input =
      letIn(appOp(n_B, n_x) ? "i", declOp("B", n_y, OperParam("y")).typedOperDecl(types, "iTOi")).typed(types, "i")
    val output = new LetInExpander(new IdleTracker(), keepNullary = keepNullary)(input)
    val expected = n_x
    assert(expected == output)
    assert(output.eqTyped(expected))
  }

  test("Test 3a: LetInExpander, keepNullary = false") {
    test3(false)
  }

  test("Test 3b: LetInExpander, keepNullary = true") {
    test3(true)
  }

  test("Test 4a: LetInExpander, keepNullary = false") {
    val n_p = tla.name("p").typed(IntT1())
    val n_a = tla.name("a").typed(IntT1())
    val n_b = tla.name("b").typed(IntT1())
    val n_c = tla.name("c").typed(IntT1())
    val n_Y = tla.name("Y").typed(types, "U")
    val n_X = tla.name("X").typed(types, "iiTOb")
    val input =
      letIn(
          ite(
              ge(n_c, int(0)) ? "b",
              letIn(
                  appOp(n_Y) ? "i",
                  declOp("Y", appOp(n_X, n_c, n_c) ? "i").typedOperDecl(types, "U")
              ) ? "b",
              appOp(n_X, n_p, int(3)) ? "b"
          ) ? "b",
          declOp("X", ge(plus(n_a, n_b) ? "i", int(0)) ? "b", OperParam("a"), OperParam("b")).typedOperDecl(types,
              "iiTOb")
      ).typed(types, "i")
    val output = new LetInExpander(new IdleTracker(), keepNullary = false)(input)
    val expected =
      ite(
          ge(n_c, int(0)) ? "b",
          ge(plus(n_c, n_c) ? "i", int(0)) ? "b",
          ge(plus(n_p, int(3)) ? "i", int(0)) ? "b"
      ).typed(types, "b")

    assert(expected == output)
    assert(output.eqTyped(expected))
  }

  test("Test 4b: LetInExpander, keepNullary = true") {
    val n_p = tla.name("p").typed(IntT1())
    val n_a = tla.name("a").typed(IntT1())
    val n_b = tla.name("b").typed(IntT1())
    val n_c = tla.name("c").typed(IntT1())
    val n_Y = tla.name("Y").typed(types, "U")
    val n_X = tla.name("X").typed(types, "iiTOb")
    val input =
      letIn(
          ite(
              ge(n_c, int(0)) ? "b",
              letIn(
                  appOp(n_Y) ? "i",
                  declOp("Y", appOp(n_X, n_c, n_c) ? "b").typedOperDecl(types, "U")
              ) ? "b",
              appOp(n_X, n_p, int(3)) ? "b"
          ) ? "b",
          declOp("X", ge(plus(n_a, n_b) ? "i", int(0)) ? "b", OperParam("a"), OperParam("b")).typedOperDecl(types,
              "iiTOb")
      ).typed(types, "i")
    val output = new LetInExpander(new IdleTracker(), keepNullary = true)(input)
    val expected =
      ite(
          ge(n_c, int(0)) ? "b",
          letIn(
              appOp(n_Y) ? "i",
              declOp("Y", ge(plus(n_c, n_c) ? "i", int(0)) ? "b").typedOperDecl(types, "U")
          ) ? "b",
          ge(plus(n_p, int(3)) ? "i", int(0)) ? "b"
      ).typed(types, "b")

    assert(expected == output)
    assert(output.eqTyped(expected))
  }

  test("Test 5: LetInExpander and LAMBDA") {
    val transformation = new LetInExpander(new IdleTracker(), keepNullary = false)
    // this is how we represent LAMBDA in IR
    val lambdaAsLetIn =
      letIn(name("LAMBDA") ? "iTOb",
          declOp("LAMBDA", eql(name("x") ? "i", name("e") ? "i") ? "b", OperParam("x"))
            .typedOperDecl(types, "iTOi"))
    val input = selectseq(name("s") ? "si", lambdaAsLetIn ? "iTOb").typed(types, "si")
    val output = transformation(input)
    // there is nothing to expand here, as SelectSeq is the standard operator
    assert(output == input)
  }

  test("Test 6: Do not expand LAMBDA") {
    val transformation = new LetInExpander(new IdleTracker(), keepNullary = false)
    // this is how we represent LAMBDA in IR
    val lambdaAsLetIn =
      letIn(name("LAMBDA") ? "iTOb",
          declOp("LAMBDA", eql(name("x") ? "i", name("e") ? "i") ? "b", OperParam("x"))
            .typedOperDecl(types, "iTOi"))
    // in this case, we cannot do anything, as the lambda operator is passed into the built-in operator
    val input = selectseq(name("s") ? "si", lambdaAsLetIn ? "iTOb").typed(types, "si")
    val output = transformation(input)
    // there is nothing to expand here, as SelectSeq is the standard operator
    assert(output == input)
  }

  test("Test 7: Expand LAMBDA when it is applied to an argument") {
    val transformation = new LetInExpander(new IdleTracker(), keepNullary = false)
    // this is how we represent LAMBDA in IR
    val lambdaAsLetIn =
      letIn(name("LAMBDA") ? "iTOb",
          declOp("LAMBDA", eql(name("x") ? "i", name("e") ? "i") ? "b", OperParam("x"))
            .typedOperDecl(types, "iTOi"))
    val input = appOp(lambdaAsLetIn ? "iTOb", int(3)).typed(types, "b")
    val output = transformation(input)
    // application of the lambda expression should be replaced with the body
    val expected = eql(int(3), name("e") ? "i").typed(types, "b")
    assert(expected == output)
  }
}
