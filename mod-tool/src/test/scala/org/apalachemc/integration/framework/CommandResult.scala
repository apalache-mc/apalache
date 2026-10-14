package org.apalachemc.integration.framework

import org.scalatest.Assertions.{assert, fail, withClue}

import scala.concurrent.duration.FiniteDuration

/** Captures one Tool invocation and provides fluent assertions over its result. */
final case class CommandResult(
    arguments: Seq[String],
    exitCode: Int,
    stdout: String,
    stderr: String,
    elapsed: FiniteDuration) {

  /** Returns normalized stdout, or stderr when requested. */
  def normalizedOutput(isStderr: Boolean = false): String = OutputMatcher.normalize(selectedOutput(isStderr))

  /** Asserts that Tool exited successfully and returns this result. */
  def expectSuccess(): CommandResult = expectExit(0)

  /** Asserts that Tool returned the expected exit code and returns this result. */
  def expectExit(expected: Int): CommandResult = {
    withClue(s"Command ${renderCommand} produced:\n${renderOutput}\n") {
      assert(exitCode == expected)
    }
    this
  }

  /** Asserts that the selected output stream contains the given fragment. */
  def expectContains(fragment: String, isStderr: Boolean = false): CommandResult = {
    val actual = normalizedOutput(isStderr)
    withClue(s"Command ${renderCommand} ${streamName(isStderr)} did not contain '$fragment':\n$actual\n") {
      assert(actual.contains(fragment))
    }
    this
  }

  /** Asserts that the selected output stream does not contain the given fragment. */
  def expectNotContains(fragment: String, isStderr: Boolean = false): CommandResult = {
    val actual = normalizedOutput(isStderr)
    withClue(s"Command ${renderCommand} ${streamName(isStderr)} unexpectedly contained '$fragment':\n$actual\n") {
      assert(!actual.contains(fragment))
    }
    this
  }

  /** Matches the selected output stream against an expected output template. */
  def expectOutput(expected: String, isStderr: Boolean = false): CommandResult = {
    val actual = selectedOutput(isStderr)
    if (!OutputMatcher.matches(expected, actual)) {
      fail(OutputMatcher.mismatch(expected, actual, s"$renderCommand ${streamName(isStderr)}"))
    }
    this
  }

  private def selectedOutput(isStderr: Boolean): String = if (isStderr) stderr else stdout

  private def streamName(isStderr: Boolean): String = if (isStderr) "stderr" else "stdout"

  private def renderOutput: String =
    s"stdout:\n${normalizedOutput()}\nstderr:\n${normalizedOutput(isStderr = true)}"

  private def renderCommand: String = ("apalache-mc" +: arguments).mkString(" ")
}
