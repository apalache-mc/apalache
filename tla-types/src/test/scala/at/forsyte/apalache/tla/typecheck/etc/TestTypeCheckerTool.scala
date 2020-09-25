package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.typecheck.{TlaType1, TypeCheckerListener, TypeCheckerTool}
import org.easymock.EasyMock
import org.junit.runner.RunWith
import org.scalatest.easymock.EasyMockSugar
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import scala.io.Source

/**
  * Unit tests for the type checker as a whole.
  *
  * Remember to pass the JVM option: -DTLA-Library=$APALACHE_HOME/src/tla/
  *
  * @author Igor Konnov
  */
@RunWith(classOf[JUnitRunner])
class TestTypeCheckerTool extends FunSuite with BeforeAndAfterEach with EasyMockSugar {
  var gen: ToEtcExpr = _

  override protected def beforeEach(): Unit = {
  }

  test("the tool runs") {
    val text =
      """---- MODULE Specb -----
        |EXTENDS Integers, Typing
        |VARIABLES msgs
        |
        |TypeAssumptions ==
        |  /\ AssumeType(msgs, "Set([type: Str, val: Int])")
        |
        |Send(m) == "[type: Str, val: Int] => Bool" :>
        |  (msgs' = msgs \cup {m})
        |
        |A(x, y) == x + y
        |
        |Init ==
        |  msgs = {}
        |
        |Next ==
        |  \E i \in 1..10:
        |    Send([type |-> "1a", val |-> i])
        |================================
      """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(locationStore)
      .loadFromSource("Specb", Source.fromString(text))

    val mod = modules(rootName)

    val listener = mock[TypeCheckerListener]

    expecting {
      // lots of types found
      listener.onTypeFound(EasyMock.anyObject[ExactRef], EasyMock.anyObject[TlaType1]).anyTimes()
      // but no type errors
    }
    whenExecuting(listener) {
      val isWellTyped = new TypeCheckerTool().check(listener, mod)
      assert(isWellTyped)
    }
  }
}