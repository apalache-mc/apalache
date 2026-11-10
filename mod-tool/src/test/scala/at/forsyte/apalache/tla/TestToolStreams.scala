package at.forsyte.apalache.tla

import org.scalatest.funsuite.AnyFunSuite

import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files
import scala.jdk.CollectionConverters._
import scala.util.Using

class TestToolStreams extends AnyFunSuite {
  private class Output {
    val bytes = new ByteArrayOutputStream
    var closed = false
    val stream = new PrintStream(bytes, true, UTF_8) {
      override def close(): Unit = { closed = true; super.close() }
    }
    def text: String = bytes.toString(UTF_8)
  }

  test("stream-aware invocations isolate output, return exit codes, and restore caller streams") {
    val previousOut = System.out
    val previousErr = System.err
    val first = new Output
    val second = new Output
    val invalid = new Output

    assert(Tool.run(Array("help"), first.stream, first.stream) == 0)
    val firstText = first.text
    assert(firstText.nonEmpty)
    assert(Tool.run(Array("help"), second.stream, second.stream) == 0)
    assert(second.text.nonEmpty)
    assert(first.text == firstText)
    assert(Tool.run(Array("--not-a-valid-option"), invalid.stream, invalid.stream) != 0)
    assert(invalid.text.nonEmpty)
    assert(System.out eq previousOut)
    assert(System.err eq previousErr)
    assert(!first.closed && !second.closed && !invalid.closed)
  }

  test("sequential parse jobs do not retain the previous job stream") {
    val directory = Files.createTempDirectory("tool-streams")
    try {
      def parse(name: String, output: Output): Int = {
        val source = Files.writeString(directory.resolve(name + ".tla"), s"---- MODULE $name ----\nValue == 1\n====\n")
        Tool.run(Array("parse", s"--out-dir=${directory.resolve(name + "-out")}", source.toString), output.stream,
            output.stream)
      }
      val first = new Output
      val second = new Output
      assert(parse("First", first) == 0)
      val saved = first.text
      assert(saved.contains("EXITCODE: OK"))
      assert(parse("Second", second) == 0)
      assert(second.text.contains("EXITCODE: OK"))
      assert(first.text == saved)
      assert(!first.closed && !second.closed)
      // Close the second job's logging files before deleting its output directory.
      Tool.run(Array("version"), second.stream, second.stream)
    } finally {
      Using.resource(Files.walk(directory)) { paths =>
        paths.iterator().asScala.toSeq.sortBy(_.getNameCount).reverse.foreach(Files.deleteIfExists)
      }
    }
  }
}
