package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSeqOper}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TransformationTracker
}
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestLetInExpander extends FunSuite with TestingPredefs {
  import Builder._

  test("Test LetInExpander, skip0Arity = false") {
    val transformation = LetInExpander(new IdleTracker(), keepNullary = false)

    val ex1 = n_x
    val ex2 = letIn(appOp(n_A), declOp("A", n_x))
    val ex3 = letIn(appOp(n_A, n_x), declOp("A", n_y, SimpleFormalParam("y")))
    val ex4 =
      letIn(
        ite(
          ge(n_c, int(0)),
          letIn(
            appOp(NameEx("Y")),
            declOp("Y", appOp(NameEx("X"), n_c, n_c))
          ),
          appOp(NameEx("X"), n_p, int(3))
        ),
        declOp("X", ge(plus(n_a, n_b), int(0)), "a", "b")
      )

    val expected1 = n_x
    val expected2 = n_x
    val expected3 = n_x
    val expected4 =
      ite(
        ge(n_c, int(0)),
        ge(plus(n_c, n_c), int(0)),
        ge(plus(n_p, int(3)), int(0))
      )

    val exs = Seq(ex1, ex2, ex3, ex4)
    val expected = Seq(expected1, expected2, expected3, expected4)
    val actual = exs map transformation

    assert(expected == actual)

  }

  test("Test LetInExpander, skip0Arity = true") {
    val transformation = LetInExpander(new IdleTracker(), keepNullary = true)

    val ex1 = n_x
    val ex2 = letIn(appOp(n_A), declOp("A", n_x))
    val ex3 = letIn(appOp(n_A, n_x), declOp("A", n_y, SimpleFormalParam("y")))
    val ex4 =
      letIn(
        ite(
          ge(n_c, int(0)),
          letIn(
            appOp(NameEx("Y")),
            declOp("Y", appOp(NameEx("X"), n_c, n_c))
          ),
          appOp(NameEx("X"), n_p, int(3))
        ),
        declOp("X", ge(plus(n_a, n_b), int(0)), "a", "b")
      )

    val expected1 = n_x
    val expected2 = letIn(appOp(n_A), declOp("A", n_x))
    val expected3 = n_x
    val expected4 =
      ite(
        ge(n_c, int(0)),
        letIn(
          appOp(NameEx("Y")),
          declOp("Y", ge(plus(n_c, n_c), int(0)))
        ),
        ge(plus(n_p, int(3)), int(0))
      )

    val exs = Seq(ex1, ex2, ex3, ex4)
    val expected = Seq(expected1, expected2, expected3, expected4)
    val actual = exs map transformation

    assert(expected == actual)

  }

  test("Test LetInExpander and LAMBDA") {
    val transformation = LetInExpander(new IdleTracker(), keepNullary = false)
    // this is how we represent LAMBDA in IR
    val lambdaAsLetIn = tla.letIn(
      tla.name("LAMBDA"),
      tla.declOp(
        "LAMBDA",
        tla.eql(tla.name("x"), tla.name("e")),
        SimpleFormalParam("x")
      )
    )
    val input = OperEx(TlaSeqOper.selectseq, tla.name("s"), lambdaAsLetIn)
    val output = transformation(input)
    // there is nothing to expand here, as SelectSeq is the standard operator
    assert(output == input)
  }

  test("Do not expand LAMBDA") {
    val transformation = LetInExpander(new IdleTracker(), keepNullary = false)
    // this is how we represent LAMBDA in IR
    val lambdaAsLetIn = tla.letIn(
      tla.name("LAMBDA"),
      tla.declOp(
        "LAMBDA",
        tla.eql(tla.name("x"), tla.name("e")),
        SimpleFormalParam("x")
      )
    )
    // in this case, we cannot do anything, as the lambda operator is passed into the built-in operator
    val input = OperEx(TlaSeqOper.selectseq, tla.name("s"), lambdaAsLetIn)
    val output = transformation(input)
    // there is nothing to expand here, as SelectSeq is the standard operator
    assert(output == input)
  }

  test("Expand LAMBDA when it is applied to an argument") {
    val transformation = LetInExpander(new IdleTracker(), keepNullary = false)
    // this is how we represent LAMBDA in IR
    val lambdaAsLetIn = tla.letIn(
      tla.name("LAMBDA"),
      tla.declOp(
        "LAMBDA",
        tla.eql(tla.name("x"), tla.name("e")),
        SimpleFormalParam("x")
      )
    )
    val input = OperEx(TlaOper.apply, lambdaAsLetIn, ValEx(TlaInt(3)))
    val output = transformation(input)
    // application of the lambda expression should be replaced with the body
    val expected = tla.eql(ValEx(TlaInt(3)), tla.name("e"))
    assert(expected == output)
  }
}
