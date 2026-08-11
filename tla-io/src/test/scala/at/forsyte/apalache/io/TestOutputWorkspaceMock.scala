package at.forsyte.apalache.io

import org.scalatest.funsuite.AnyFunSuite

import java.nio.file.Files

class TestOutputWorkspaceMock extends AnyFunSuite {

  test("ordinary writes are executed and discarded without creating files") {
    val root = Files.createTempDirectory("output-workspace-mock-test")
    val output = root.resolve("discarded.txt")
    var callbackWasInvoked = false

    try {
      OutputWorkspaceMock.withWriter(output) { writer =>
        callbackWasInvoked = true
        writer.print("discarded")
      }
      assert(callbackWasInvoked)
      assert(!Files.exists(output))
    } finally {
      Files.delete(root)
    }
  }

  test("optional writes are disabled") {
    var intermediateCallbackWasInvoked = false
    var profilingCallbackWasInvoked = false

    OutputWorkspaceMock.withWriterInIntermediateDir("discarded.txt") { _ =>
      intermediateCallbackWasInvoked = true
    }
    val profilingWasWritten = OutputWorkspaceMock.withProfilingWriter { _ =>
      profilingCallbackWasInvoked = true
    }

    assert(!intermediateCallbackWasInvoked)
    assert(!profilingCallbackWasInvoked)
    assert(!profilingWasWritten)
  }
}
