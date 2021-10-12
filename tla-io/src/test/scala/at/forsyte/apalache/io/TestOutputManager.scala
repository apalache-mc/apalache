package at.forsyte.apalache.io

import at.forsyte.apalache.io.annotations.{Annotation, AnnotationBool, AnnotationStr, PrettyWriterWithAnnotations}
import at.forsyte.apalache.io.annotations.store.createAnnotationStore
import at.forsyte.apalache.tla.lir._
import UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.io.lir.TextLayout
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import java.io.{PrintWriter, StringWriter}

@RunWith(classOf[JUnitRunner])
class TestOutputManager extends FunSuite with BeforeAndAfterEach {
  test("X") {
    OutputManager.syncFromCFG()
  }
}
