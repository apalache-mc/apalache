package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.typecheck.{TypeCheckerListener, TypeCheckerTool}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.lir.{TlaModule, TlaType1, Typed, TypingException, UID}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.io.typecheck.parser.{DefaultType1Parser, Type1Parser}
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

  private val megaSpec = "MegaSpec1"
  private val tlcSpec = "TlcSpec1"

  override def beforeEach() {
    sourceStore = new SourceStore()
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
    parser = DefaultType1Parser
  }

  def loadSpecFromResource(name: String): Source = {
    // Previously, we were using fromResource, but it was too unstable across environments
    // (e.g., it failed in Intellij Idea). Now we are just reading it from the current working directory.
    Source.fromFile(s"src/test/resources/$name.tla")
  }

  test("the tool runs and reports no type errors") {
    val (rootName, modules) =
      sanyImporter.loadFromSource(megaSpec, loadSpecFromResource(megaSpec))

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
      val typechecker = new TypeCheckerTool(annotationStore, true)
      val isWellTyped = typechecker.check(listener, mod)
      assert(isWellTyped)
    }
  }

  test("the tool runs and tags all expressions") {
    val (rootName, modules) =
      sanyImporter.loadFromSource(megaSpec, loadSpecFromResource(megaSpec))

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
      val typechecker = new TypeCheckerTool(annotationStore, true)

      def defaultTag(uid: UID): Nothing = {
        throw new TypingException("No type for UID: " + uid, uid)
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

  test("the tool consumes its output on MegaSpec1") {
    typecheckSpec("MegaSpec1")
  }

  // fixing this test is scheduled in: https://github.com/informalsystems/apalache/issues/1255
  ignore("the tool consumes its output on TlcSpec1") {
    typecheckSpec("TlcSpec1")
  }

  private def typecheckSpec(specName: String): Unit = {
    val (rootName, modules) =
      sanyImporter.loadFromSource(specName, loadSpecFromResource(specName))

    val mod = modules(rootName)

    def defaultTag(uid: UID): Nothing = {
      throw new TypingException("No type for UID: " + uid, uid)
    }

    val listener = mock[TypeCheckerListener]
    expecting {
      // lots of types found
      listener
        .onTypeFound(EasyMock.anyObject[ExactRef], EasyMock.anyObject[TlaType1])
        .anyTimes()
      // but no type errors
    }
    whenExecuting(listener) {
      val typechecker = new TypeCheckerTool(annotationStore, true)

      val output = typechecker.checkAndTag(new IdleTracker(), listener, defaultTag, mod)
      assert(output.isDefined)

      val typechecker2 = new TypeCheckerTool(annotationStore, true)
      val output2 = typechecker2.checkAndTag(new IdleTracker(), listener, defaultTag, output.get)
      assert(output2.isDefined)
    }
  }
}
