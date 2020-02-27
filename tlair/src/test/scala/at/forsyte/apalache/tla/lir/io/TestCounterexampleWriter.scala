package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.FunSuite

@RunWith(classOf[JUnitRunner])
class TestCounterexampleWriter extends FunSuite {


  def compare(kind: String, rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState], expected: String): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = CounterexampleWriter(kind, printWriter)
    writer.write(rootModule, notInvariant, states)
    printWriter.flush()
    assert(stringWriter.toString.replaceFirst("Created by Apalache on .*\n", "Created by Apalache on DATETIME\n") == expected)
  }

  test("single state") {
    compare("tla",
      new TlaModule("test",List()),
      gt(name("x"), int(1)),
      List(
        ("",Map("x" -> int(2)))
      ),
      """------------------------- MODULE counterexample -------------------------
        |
        |EXTENDS test
        |
        |(* Initial state *)
        |
        |State1 == x = 2
        |
        |(* The following formula holds true in the last state and violates the invariant *)
        |
        |InvariantViolation == x > 1
        |
        |================================================================================
        |\* Created by Apalache on DATETIME
        |\* https://github.com/konnov/apalache
        |""".stripMargin
    )
  }

    test("two steps") {
      compare("tla",
        new TlaModule("test",List()),
        gt(name("x"), int(1)),
        List(
          ("", Map("x" -> int(0))),
          ("Trans1", Map("x" -> int(1))),
          ("Trans2", Map("x" -> int(2)))
        ),
        """------------------------- MODULE counterexample -------------------------
          |
          |EXTENDS test
          |
          |(* Initial state *)
          |
          |State1 == x = 0
          |
          |(* Transition Trans1 to State2 *)
          |
          |State2 == x = 1
          |
          |(* Transition Trans2 to State3 *)
          |
          |State3 == x = 2
          |
          |(* The following formula holds true in the last state and violates the invariant *)
          |
          |InvariantViolation == x > 1
          |
          |================================================================================
          |\* Created by Apalache on DATETIME
          |\* https://github.com/konnov/apalache
          |""".stripMargin
      )
    }

  test("two steps with conjunction") {
    compare("tla",
      new TlaModule("test",List()),
      and(gt(name("x"), int(1)), eql(name("y"), int(10))),
      List(
        ("",Map("x" -> int(0), "y" -> int(8))),
        ("Trans1", Map("x" -> int(1), "y" -> int(9))),
        ("Trans2", Map("x" -> int(2), "y" -> int(10)))
      ),
      """------------------------- MODULE counterexample -------------------------
        |
        |EXTENDS test
        |
        |(* Initial state *)
        |
        |State1 == x = 0 /\ y = 8
        |
        |(* Transition Trans1 to State2 *)
        |
        |State2 == x = 1 /\ y = 9
        |
        |(* Transition Trans2 to State3 *)
        |
        |State3 == x = 2 /\ y = 10
        |
        |(* The following formula holds true in the last state and violates the invariant *)
        |
        |InvariantViolation == x > 1 /\ y = 10
        |
        |================================================================================
        |\* Created by Apalache on DATETIME
        |\* https://github.com/konnov/apalache
        |""".stripMargin
    )
  }

  test("TLC single state") {
    compare("tlc",
      new TlaModule("test",List()),
      gt(name("x"), int(1)),
      List(
        ("",Map("x" -> int(2)))
      ),
      """@!@!@STARTMSG 2262:0 @!@!@
        |Created by Apalache on DATETIME
        |@!@!@ENDMSG 2262 @!@!@
        |@!@!@STARTMSG 2110:1 @!@!@
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
    compare("tlc",
      new TlaModule("test",List()),
      gt(name("x"), int(1)),
      List(
        ("", Map("x" -> int(0))),
        ("Next", Map("x" -> int(1))),
        ("Next", Map("x" -> int(2)))
      ),
      """@!@!@STARTMSG 2262:0 @!@!@
        |Created by Apalache on DATETIME
        |@!@!@ENDMSG 2262 @!@!@
        |@!@!@STARTMSG 2110:1 @!@!@
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
    compare("tlc",
      new TlaModule("test",List()),
      and(gt(name("x"), int(1)), eql(name("y"), int(10))),
      List(
        ("", Map("x" -> int(0), "y" -> int(8))),
        ("Trans1", Map("x" -> int(1), "y" -> int(9))),
        ("Trans2", Map("x" -> int(2), "y" -> int(10)))
      ),
      """@!@!@STARTMSG 2262:0 @!@!@
        |Created by Apalache on DATETIME
        |@!@!@ENDMSG 2262 @!@!@
        |@!@!@STARTMSG 2110:1 @!@!@
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
