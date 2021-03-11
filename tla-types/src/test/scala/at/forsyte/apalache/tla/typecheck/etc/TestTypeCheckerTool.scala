package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.typecheck.{TlaType1, Type1Parser, TypeCheckerListener, TypeCheckerTool, TypingException}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.lir.{Typed, UID}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
import org.easymock.EasyMock
import org.junit.runner.RunWith
import org.scalatest.easymock.EasyMockSugar
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import scala.io.Source

/**
 * Unit tests for the type checker as a tool.
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

  def getMegaSpec1: Source = {
    Source.fromResource("MegaSpec1.tla")
  }

  test("the tools runs and reports no type errors") {
    val (rootName, modules) =
      sanyImporter.loadFromSource("MegaSpec1", getMegaSpec1)

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
      sanyImporter.loadFromSource("MegaSpec1", getMegaSpec1)

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

      def defaultTag(uid: UID): Nothing = {
        throw new TypingException("No type for UID: " + uid)
      }

      typechecker.checkAndTag(new IdleTracker(), listener, defaultTag, mod) match {
        case None =>
          fail("Expected the specification to be well-typed")

        case Some(output) =>
          // there was no exception, so all expressions and declarations should be tagged with a type
          val msgsType = parser("Set([type: Str, val: Int])")
          assert(Typed(msgsType) == output.varDeclarations.head.typeTag)
      }
    }
  }

  test("the tools consumes its output") {
    val (rootName, modules) =
      sanyImporter.loadFromSource("MegaSpec1", getMegaSpec1)

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

      def defaultTag(uid: UID): Nothing = {
        throw new TypingException("No type for UID: " + uid)
      }

      val output = typechecker.checkAndTag(new IdleTracker(), listener, defaultTag, mod)
      assert(output.isDefined)
      val output2 = typechecker.checkAndTag(new IdleTracker(), listener, defaultTag, output.get)
      assert(output2.isDefined)
    }
  }
}
