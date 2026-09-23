package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.io.json.DefaultTagJsonReader
import at.forsyte.apalache.io.json.ujsonimpl.{TlaToUJson, UJsonToTla}
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs
import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.lir.src.SourceStore
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.{DefaultTypeCheckerListener, TypeCheckerListener, TypeCheckerTool}
import at.forsyte.apalache.tla.types.parser.{DefaultType1Parser, Type1Parser}
import com.typesafe.scalalogging.LazyLogging
import org.easymock.EasyMock
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.easymock.EasyMockSugar
import org.scalatestplus.junit.JUnitRunner

import scala.collection.mutable
import scala.io.Source

/**
 * Unit tests for the type checker as a tool.
 *
 * @author
 *   Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestTypeCheckerTool extends AnyFunSuite with BeforeAndAfterEach with EasyMockSugar with LazyLogging {
  var gen: ToEtcExpr = _
  private var sourceStore: SourceStore = _
  private var annotationStore: AnnotationStore = _
  private var sanyImporter: SanyImporter = _
  private var parser: Type1Parser = _

  private val megaSpec = "MegaSpec1"

  override def beforeEach(): Unit = {
    sourceStore = new SourceStore()
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
    parser = DefaultType1Parser
  }

  def loadSpecFromResource(name: String): Source = {
    // Previously, we were using fromResource, but it was too unstable across environments
    // (e.g., it failed in Intellij Idea). Now we are just reading it from $APALACHE_HOME/passes/src/test/resources.
    // This is consistent with the behavior of SanyImporter when it is run in tests.
    System.getenv("APALACHE_HOME") match {
      // Warn if environment variable APALACHE_HOME is not set
      case null =>
        logger.error("Not running from fat JAR and APALACHE_HOME is not set.")
        logger.error("Set APALACHE_HOME to a directory where Apalache has been checked out.")
        throw new IllegalStateException("Missing APALACHE_HOME to run the tests")

      case apalacheHome: String =>
        Source.fromFile(s"$apalacheHome/passes/src/test/resources/$name.tla")
    }
  }

  test("the tool runs and reports no type errors") {
    val (rootName, modules) =
      sanyImporter.loadFromSource(loadSpecFromResource(megaSpec))

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
      val typechecker = new TypeCheckerTool(annotationStore, true, useRows = false)
      val isWellTyped = typechecker.check(listener, mod)
      assert(isWellTyped)
    }
  }

  test("the tool runs and tags all expressions") {
    val (rootName, modules) =
      sanyImporter.loadFromSource(loadSpecFromResource(megaSpec))

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
      val typechecker = new TypeCheckerTool(annotationStore, true, useRows = false)

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

  test("the tool consumes its TLA output on MegaSpec1") {
    typecheckSpec("MegaSpec1")
  }

  test("the tool consumes its JSON output on MegaSpec1") {
    typecheckSpecAndEncoding("MegaSpec1")
  }

  test("the tool consumes its output on TlcSpec1") {
    typecheckSpec("TlcSpec1")
  }

  test("local definitions constrain the types of enclosing operators") {
    val (rootName, modules) = sanyImporter.loadFromSource(loadSpecFromResource("LetPolyRegression"))
    val module = modules(rootName)
    val expectedType = parser("Int => Int")

    for (inferPoly <- Seq(true, false)) {
      val typechecker = new TypeCheckerTool(annotationStore, inferPoly, useRows = false)
      val tagged = typechecker.checkAndTag(new IdleTracker(), new DefaultTypeCheckerListener(),
          uid => throw new TypingException("No type for UID: " + uid, uid), module)
      assert(tagged.isDefined)
      val operators = tagged.get.operDeclarations.map(d => d.name -> d).toMap
      for (name <- Seq("Direct", "ViaLet", "ViaLetIf", "ViaLocal", "ViaNested")) {
        assert(operators(name).typeTag == Typed(expectedType), name)
      }
    }
  }

  test("a bad call to an operator constrained through LET is a type error") {
    val (rootName, modules) = sanyImporter.loadFromSource(loadSpecFromResource("LetPolyBadCall"))
    val errors = mutable.ListBuffer.empty[String]
    val listener = new DefaultTypeCheckerListener() {
      override def onTypeError(sourceRef: EtcRef, message: String): Unit = errors += message
    }
    val typechecker = new TypeCheckerTool(annotationStore, inferPoly = true, useRows = false)
    assert(!typechecker.check(listener, modules(rootName)))
    assert(errors.exists(_.contains("Set(Bool)")), errors.mkString("\n"))
  }

  test("shared LET types are final on every callback, including after JSON round-tripping") {
    val (rootName, modules) = sanyImporter.loadFromSource(loadSpecFromResource("LetSharedTypes"))
    val listener = new DefaultTypeCheckerListener() {
      override def onTypeFound(sourceRef: ExactRef, tp: TlaType1): Unit = {
        // Check every notification, not just the last type recorded for each UID. Like the production listener
        // with --infer-poly=false, this must reject provisional polymorphic types immediately.
        assert(tp.isMono, s"Provisional type $tp at $sourceRef")
      }
      override def onTypeError(sourceRef: EtcRef, message: String): Unit = fail(message)
    }
    val enc = new TlaToUJson(locatorOpt = None)(TlaType1PrinterPredefs.printer)
    val dec = new UJsonToTla(sourceStoreOpt = None)(DefaultTagJsonReader)
    for (inferPoly <- Seq(true, false); useRows <- Seq(true, false)) {
      val typechecker = new TypeCheckerTool(annotationStore, inferPoly, useRows)
      val tagged = typechecker
        .checkAndTag(new IdleTracker(), listener, uid => throw new TypingException("No type for UID: " + uid, uid),
            modules(rootName))
        .get
      val operators = tagged.operDeclarations.map(d => d.name -> d).toMap
      for (name <- Seq("F", "Reversed", "ViaBody")) {
        assert(operators(name).typeTag == Typed(parser("Int => Bool")))
      }
      for (name <- Seq("Nested", "ViaRecord")) {
        assert(operators(name).typeTag == Typed(parser("Int => Int")))
      }
      assert(operators("Alias").typeTag == Typed(parser("(Int, Int) => Int")))
      assert(operators("ViaSet").typeTag == Typed(parser("Set(Int) => Set(Int)")))
      assert(typechecker.check(listener, dec.asTlaModule(enc(tagged))))
    }
  }

  test("a local operator can share a captured type while generalizing its own parameter") {
    val (rootName, modules) = sanyImporter.loadFromSource(Source.fromString("""
        |---- MODULE MixedLet ----
        |EXTENDS Integers
        |F(n) == LET K(y) == [captured |-> n, value |-> y]
        |            c == n + 1
        |        IN K(TRUE).value /\ K(1).value = 1 /\ c > 0
        |====
        |""".stripMargin))
    for (useRows <- Seq(true, false)) {
      val typechecker = new TypeCheckerTool(annotationStore, inferPoly = true, useRows)
      val tagged = typechecker
        .checkAndTag(new IdleTracker(), new DefaultTypeCheckerListener(),
            uid => throw new TypingException("No type for UID: " + uid, uid), modules(rootName))
        .get
      val f = tagged.operDeclarations.find(_.name == "F").get
      assert(f.typeTag == Typed(parser("Int => Bool")))
      val k = f.body.asInstanceOf[LetInEx].decls.find(_.name == "K").get
      val signature = TlaType1.fromTypeTag(k.typeTag)
      assert(signature.usedNames.size == 1)
      val a = VarT1(signature.usedNames.head)
      val fields = Seq("captured" -> IntT1, "value" -> a)
      val result = if (useRows) RecRowT1(RowT1(fields: _*)) else RecT1(fields: _*)
      assert(signature == OperT1(Seq(a), result))
      assert(k.body.typeTag == Typed(result))
    }
  }

  private def typecheckSpecAndEncoding(specName: String): Unit = {
    val (rootName, modules) =
      sanyImporter.loadFromSource(loadSpecFromResource(specName))

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

    val dec = new UJsonToTla(sourceStoreOpt = None)(DefaultTagJsonReader)
    val enc = new TlaToUJson(locatorOpt = None)(TlaType1PrinterPredefs.printer)

    whenExecuting(listener) {
      val typechecker = new TypeCheckerTool(annotationStore, true, useRows = false)

      val output = typechecker.checkAndTag(new IdleTracker(), listener, defaultTag, mod)
      assert(output.isDefined)

      val postModule = output.get

      val deserializaedSerialization = dec.asTlaModule(enc(postModule))

      deserializaedSerialization.declarations.zip(postModule.declarations).map { case (d1, d2) =>
        assert(d1.eqTyped(d2))
      }

    }
  }

  private def typecheckSpec(specName: String): Unit = {
    val (rootName, modules) =
      sanyImporter.loadFromSource(loadSpecFromResource(specName))

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
      val typechecker = new TypeCheckerTool(annotationStore, true, useRows = false)

      val output = typechecker.checkAndTag(new IdleTracker(), listener, defaultTag, mod)
      assert(output.isDefined)

      val typechecker2 = new TypeCheckerTool(annotationStore, true, useRows = false)
      val output2 = typechecker2.checkAndTag(new IdleTracker(), listener, defaultTag, output.get)
      assert(output2.isDefined)
    }
  }
}
