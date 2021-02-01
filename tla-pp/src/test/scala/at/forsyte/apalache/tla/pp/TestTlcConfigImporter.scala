package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.io.tlc.TlcConfigParserApalache
import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import java.io.{PrintWriter, StringWriter}
import scala.io.Source

@RunWith(classOf[JUnitRunner])
class TestTlcConfigImporter extends FunSuite with BeforeAndAfterEach {
  private var sourceStore: SourceStore = _
  private var annotationStore: AnnotationStore = _
  private var sanyImporter: SanyImporter = _

  override def beforeEach() {
    sourceStore = new SourceStore()
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
  }

  def configureAndCompare(tla: String, tlc: String, expected: String) = {
    val config = TlcConfigParserApalache(tlc)
    val (rootName, modules) =
      sanyImporter.loadFromSource("test", Source.fromString(tla))
    val mod = modules(rootName)
    val mod2 = new TlcConfigImporter(config, new IdleTracker())(mod)
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(mod2)
    printWriter.flush()
    assert(stringWriter.toString == expected)
  }

  test("INIT-NEXT") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |INIT Init
        |NEXT Next
      """.stripMargin,
        """----- MODULE test -----
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("SPECIFICATION") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |SPECIFICATION Spec
      """.stripMargin,
        """----- MODULE test -----
        |
        |SPECIFICATION == Spec
        |===============
        |""".stripMargin
    )
  }

  test("CONSTANT assignments") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |CONSTANT
        |N = M
        |K = L
        |INIT Init
        |NEXT Next
      """.stripMargin,
        """----- MODULE test -----
        |
        |OVERRIDE_N == "ModelValue_M"
        |
        |OVERRIDE_K == "ModelValue_L"
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("CONSTANT assignments and SYMMETRY") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |CONSTANT
        |N = M
        |\* symmetry definitions are skipped by our parser
        |SYMMETRY symmDef1
        |CONSTANT K = L
        |INIT Init
        |NEXT Next
      """.stripMargin,
        """----- MODULE test -----
        |
        |OVERRIDE_N == "ModelValue_M"
        |
        |OVERRIDE_K == "ModelValue_L"
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("CONSTANT replacements") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |CONSTANT
        |A <- B
        |C <- D
        |INIT Init
        |NEXT Next
      """.stripMargin,
        """----- MODULE test -----
        |
        |OVERRIDE_A == B
        |
        |OVERRIDE_C == D
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("CONSTANT assignments and replacements") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |CONSTANTS
        |N = M
        |A <- B
        |K = L
        |C <- D
        |INIT Init
        |NEXT Next
      """.stripMargin,
        """----- MODULE test -----
        |
        |OVERRIDE_N == "ModelValue_M"
        |
        |OVERRIDE_K == "ModelValue_L"
        |
        |OVERRIDE_A == B
        |
        |OVERRIDE_C == D
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("INIT-NEXT and INVARIANTS") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |INIT Init
        |NEXT Next
        |INVARIANT Inv1
        |INVARIANTS Inv2
      """.stripMargin,
        """----- MODULE test -----
        |
        |INVARIANT_$0 == Inv1
        |
        |INVARIANT_$1 == Inv2
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("INIT-NEXT and PROPERTIES") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |INIT Init
        |NEXT Next
        |PROPERTY Prop1
        |PROPERTIES Prop2
      """.stripMargin,
        """----- MODULE test -----
        |
        |PROPERTY_$0 == Prop1
        |
        |PROPERTY_$1 == Prop2
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("INIT-NEXT and CONSTRAINTS") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |CONSTRAINTS Cons1
        |Cons2
        |INIT Init
        |NEXT Next
      """.stripMargin,
        """----- MODULE test -----
        |
        |CONSTRAINT_$0 == Cons1
        |
        |CONSTRAINT_$1 == Cons2
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("INIT-NEXT and ACTION_CONSTRAINTS") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |ACTION_CONSTRAINTS Cons1
        |Cons2
        |INIT Init
        |NEXT Next
      """.stripMargin,
        """----- MODULE test -----
        |
        |ACTION_CONSTRAINT_$0 == Cons1
        |
        |ACTION_CONSTRAINT_$1 == Cons2
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }

  test("all features") {
    configureAndCompare(
        """---- MODULE test ----
        |================================
      """.stripMargin,
        """
        |CONSTANTS
        |N = M
        |A <- B
        |CONSTRAINT
        |Cons1
        |ACTION_CONSTRAINT
        |Cons2
        |INIT Init
        |NEXT Next
        |INVARIANT
        |Inv
        |PROPERTY
        |Prop
      """.stripMargin,
        """----- MODULE test -----
        |
        |OVERRIDE_N == "ModelValue_M"
        |
        |OVERRIDE_A == B
        |
        |CONSTRAINT_$0 == Cons1
        |
        |ACTION_CONSTRAINT_$0 == Cons2
        |
        |INVARIANT_$0 == Inv
        |
        |PROPERTY_$0 == Prop
        |
        |INIT == Init
        |
        |NEXT == Next
        |===============
        |""".stripMargin
    )
  }
}
