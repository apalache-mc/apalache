package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.convenience.tla._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.FunSuite

@RunWith(classOf[JUnitRunner])
class TestCounterexampleWriter extends FunSuite {

  def compareTla(notInvariant: NotInvariant, init: State, nextStates: List[NextState], expected: String): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new TlaCounterexampleWriter(printWriter)
    writer.write(notInvariant, init, nextStates)
    printWriter.flush()
    assert(stringWriter.toString == expected)
  }

  def compareTlc(notInvariant: NotInvariant, init: State, nextStates: List[NextState], expected: String): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new TlcCounterexampleWriter(printWriter)
    writer.write(notInvariant, init, nextStates)
    printWriter.flush()
    assert(stringWriter.toString == expected)
  }


  test("single state") {
    compareTla(
      gt(name("x"), int(1)),
      Map("x" -> int(2)),
      List(),
      """(* Initial state *)
        |
        |State0 == x = 2
        |
        |(* The following formula holds true in State0 and violates the invariant *)
        |
        |InvariantViolation == x > 1
        |
        |""".stripMargin
    )
  }

    test("two steps") {
      compareTla(
        gt(name("x"), int(1)),
        Map("x" -> int(0)),
        List(
          ("Trans1", Map("x" -> int(1))),
          ("Trans2", Map("x" -> int(2)))
        ),
        """(* Initial state *)
          |
          |State0 == x = 0
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
          |
          |InvariantViolation == x > 1
          |
          |""".stripMargin
      )
    }

  test("two steps with conjunction") {
    compareTla(
      and(gt(name("x"), int(1)), eql(name("y"), int(10))),
      Map("x" -> int(0), "y" -> int(8)),
      List(
        ("Trans1", Map("x" -> int(1), "y" -> int(9))),
        ("Trans2", Map("x" -> int(2), "y" -> int(10)))
      ),
      """(* Initial state *)
        |
        |State0 == x = 0 /\ y = 8
        |
        |(* Transition Trans1 to State1 *)
        |
        |State1 == x = 1 /\ y = 9
        |
        |(* Transition Trans2 to State2 *)
        |
        |State2 == x = 2 /\ y = 10
        |
        |(* The following formula holds true in State2 and violates the invariant *)
        |
        |InvariantViolation == x > 1 /\ y = 10
        |
        |""".stripMargin
    )
  }

  test("TLC single state") {
    compareTlc(
      gt(name("x"), int(1)),
      Map("x" -> int(2)),
      List(),
      """@!@!@STARTMSG 2110:1 @!@!@
        |Invariant is violated.
        |@!@!@ENDMSG 2110 @!@!@
        |@!@!@STARTMSG 2121:1 @!@!@
        |The behavior up to this point is:
        |@!@!@ENDMSG 2121 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |1: <Initial predicate>
        |x = 2
        |
        |@!@!@ENDMSG 2217 @!@!@
        |""".stripMargin
    )
  }

  test("TLC two steps") {
    compareTlc(
      gt(name("x"), int(1)),
      Map("x" -> int(0)),
      List(
        ("Next", Map("x" -> int(1))),
        ("Next", Map("x" -> int(2)))
      ),
      """@!@!@STARTMSG 2110:1 @!@!@
        |Invariant is violated.
        |@!@!@ENDMSG 2110 @!@!@
        |@!@!@STARTMSG 2121:1 @!@!@
        |The behavior up to this point is:
        |@!@!@ENDMSG 2121 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |1: <Initial predicate>
        |x = 0
        |
        |@!@!@ENDMSG 2217 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |2: <Next>
        |x = 1
        |
        |@!@!@ENDMSG 2217 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |3: <Next>
        |x = 2
        |
        |@!@!@ENDMSG 2217 @!@!@
        |""".stripMargin
    )
  }

  test("TLC two steps with conjunction") {
    compareTlc(
      and(gt(name("x"), int(1)), eql(name("y"), int(10))),
      Map("x" -> int(0), "y" -> int(8)),
      List(
        ("Trans1", Map("x" -> int(1), "y" -> int(9))),
        ("Trans2", Map("x" -> int(2), "y" -> int(10)))
      ),
      """@!@!@STARTMSG 2110:1 @!@!@
        |Invariant is violated.
        |@!@!@ENDMSG 2110 @!@!@
        |@!@!@STARTMSG 2121:1 @!@!@
        |The behavior up to this point is:
        |@!@!@ENDMSG 2121 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |1: <Initial predicate>
        |x = 0 /\ y = 8
        |
        |@!@!@ENDMSG 2217 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |2: <Next>
        |x = 1 /\ y = 9
        |
        |@!@!@ENDMSG 2217 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |3: <Next>
        |x = 2 /\ y = 10
        |
        |@!@!@ENDMSG 2217 @!@!@
        |""".stripMargin
    )
  }
}
