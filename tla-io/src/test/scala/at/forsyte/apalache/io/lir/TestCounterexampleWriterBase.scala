package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.TlaEx
import org.scalatest.Assertions

import java.io.{PrintWriter, StringWriter}

trait TestCounterexampleWriterBase extends Assertions {

  /**
   * Write a counterexample and compare the output to the expected result.
   *
   * @param kind
   *   counterexample kind ("tla", "json", "itf.json")
   * @param rootModule
   *   the module that produced the counterexample
   * @param notInvariant
   *   the invariant violation (as an expression)
   * @param states
   *   a list of states: state 0 is the constant initializer, state 1 is the initial state, etc.
   * @param expected
   *   the expected output as a string
   */
  def compare(
      kind: String,
      trace: Trace[TlaEx],
      expected: String): Unit = {

    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = CounterexampleWriter(kind, printWriter)
    writer.write(trace)
    printWriter.flush()
    val dateErasure = stringWriter.toString.replaceFirst(
        "Created by Apalache on [A-Za-z 0-9:]*( \\*\\))?([\n\"])",
        "Created by Apalache on DATETIME$1$2",
    )
    assert(dateErasure == expected)
  }
}
