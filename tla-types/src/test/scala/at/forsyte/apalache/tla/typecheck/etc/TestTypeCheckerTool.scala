package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.typecheck.{TlaType1, Type1Parser, TypeCheckerListener, TypeCheckerTool}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.lir.Typed
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
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
  private var sourceStore: SourceStore = _
  private var annotationStore: AnnotationStore = _
  private var sanyImporter: SanyImporter = _
  private var parser: Type1Parser = _

  override def beforeEach() {
    sourceStore = new SourceStore()
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
    parser = DefaultType1Parser
  }

  // We push plenty of TLA+ constructs in this spec, to make sure that:
  // (1) the type checker does not fail, and (2) all expressions are labelled with types.
  private val specB =
    """---- MODULE Specb -----
    |EXTENDS Integers
    |CONSTANTS
    | \* @type: Int;
    | N
    |
    |ASSUME(N > 42)
    |
    |VARIABLES
    |   \* @type: Set([type: Str, val: Int]);
    |   msgs
    |
    |\* @type: [type: Str, val: Int] => Bool;
    |Send(m) ==
    |  msgs' = msgs \cup {m}
    |
    |A(x, y) ==
    |  LET Plus(a, b) == a + b IN
      |  Plus(x, y)
      |
      |Init ==
      |  msgs = {}
      |
      |Next ==
      |  /\ [type |-> "1a", val |-> 3].type = "1a"
      |  /\ \E i \in 1..10:
      |      Send([type |-> "1a", val |-> i])
      |================================
      """.stripMargin

  test("the tools runs and reports no type errors") {
    val (rootName, modules) =
      sanyImporter.loadFromSource("Specb", Source.fromString(specB))

    val mod = modules(rootName)

    val listener = mock[TypeCheckerListener]

    expecting {
      // lots of types found
      listener
        .onTypeFound(EasyMock.anyObject[ExactRef], EasyMock.anyObject[TlaType1])
        .anyTimes()
      // but no type errors
    }
    whenExecuting(listener) {
      val typechecker = new TypeCheckerTool(annotationStore, false)
      val isWellTyped = typechecker.check(listener, mod)
      assert(isWellTyped)
    }
  }

  test("the tools runs and tags all expressions") {
    val (rootName, modules) =
      sanyImporter.loadFromSource("Specb", Source.fromString(specB))

    val mod = modules(rootName)

    val listener = mock[TypeCheckerListener]

    expecting {
      // lots of types found
      listener
        .onTypeFound(EasyMock.anyObject[ExactRef], EasyMock.anyObject[TlaType1])
        .anyTimes()
      // but no type errors
    }
    whenExecuting(listener) {
      val typechecker = new TypeCheckerTool(annotationStore, false)
      typechecker.checkAndTag(new IdleTracker(), listener, mod) match {
        case None =>
          fail("Expected the specification to be well-typed")

        case Some(output) =>
          // there was no exception, so all expressions and declarations should be tagged with a type
          val msgsType = parser("Set([type: Str, val: Int])")
          assert(Typed(msgsType) == output.varDeclarations.head.typeTag)
      }
    }
  }
}
