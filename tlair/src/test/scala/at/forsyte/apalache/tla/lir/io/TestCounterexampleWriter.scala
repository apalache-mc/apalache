package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.convenience.tla._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.FunSuite

@RunWith(classOf[JUnitRunner])
class TestCounterexampleWriter extends FunSuite {

  // compare expression and expected result (single-line formatting)
  def compare(notInvariant: NotInvariant, init: State, nextStates: List[NextState], expected: String): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new TlaCounterexampleWriter(printWriter)
    writer.write(notInvariant, init, nextStates)
    printWriter.flush()
    assert(stringWriter.toString == expected)
  }


  test("single state") {
    compare(
      ("Inv", gt(name("x"), int(1))),
      ("ConstInit", Map("x" -> int(2))),
      List(),
      """(* Initial state *)
        |ConstInit == x = 2
        |
        |(* The following formula holds true in ConstInit and violates the invariant *)
        |InvariantViolation == x > 1
        |
        |""".stripMargin
    )
  }

    test("two steps") {
      compare(
        ("Inv", gt(name("x"), int(1))),
        ("ConstInit", Map("x" -> int(0))),
        List(
          ("Trans1", ("State1",Map("x" -> int(1)))),
          ("Trans2", ("State2", Map("x" -> int(2))))
        ),
        """(* Initial state *)
          |ConstInit == x = 0
          |
          |(* Transition Trans1 to State1 *)
          |
          |State1 == x = 1
          |
          |(* Transition Trans2 to State2 *)
          |
          |State2 == x = 2
          |
          |(* The following formula holds true in State2 and violates the invariant *)
          |InvariantViolation == x > 1
          |
          |""".stripMargin
      )
    }
}