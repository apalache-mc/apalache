package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla._
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestLetInApplier extends AnyFunSuite with BeforeAndAfterEach {

  private var delambda = new LetInApplier(new IdleTracker)

  override def beforeEach(): Unit = {
    delambda = new LetInApplier(new IdleTracker)
  }

  val intToIntT: TlaType1 = OperT1(Seq(IntT1), IntT1)
  val unitToIntT: TlaType1 = OperT1(Seq.empty, IntT1)

  test("""NoOp on non-(lambda applications) and non-lambda expressions""") {
    val values: Seq[TlaEx] = Seq(
        int(1),
        name("x", StrT1),
        appOp(name("Op", intToIntT), int(1)),
        appOp(name("Op", unitToIntT)),
        // LET F(p) == p + 1 IN F(1)
        letIn(
            appOp(name("F", intToIntT), int(1)),
            decl("F", plus(name("p", IntT1), int(1)), param("p", IntT1)),
        ),
    )

    val txdValues = values.map(delambda)
    assert(txdValues == values)
  }

  test("""Correct transformation on lambda applications""") {

    def letShell(body: TBuilderInstruction, operName: String = "F", paramName: String = "p"): TBuilderInstruction =
      letIn(
          body,
          decl(operName, plus(name(paramName, IntT1), int(1)), param(paramName, IntT1)),
      )

    val lambda1 = letShell(name("F", intToIntT))
    val arg1 = int(1)
    val lambdaApp1 = appOp(lambda1, arg1)
    val expected1: TlaEx = letShell(appOp(name("F", intToIntT), arg1))

    assert(delambda(lambdaApp1) == expected1)
    assert(delambda(expected1) == expected1)

    val lambda2 = letShell(name("F2", intToIntT), "F2", "p2")
    val arg2 = appOp(lambda2, int(1))
    val lambdaApp2 = appOp(lambda1, arg2)

    val expected2: TlaEx = letShell(
        appOp(
            name("F", intToIntT),
            letShell(
                appOp(name("F2", intToIntT), int(1)),
                "F2",
                "p2",
            ),
        )
    )

    assert(delambda(lambdaApp2) == expected2)
    assert(delambda(expected2) == expected2)

  }

}
