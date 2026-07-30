package at.forsyte.apalache.io.lir

import at.forsyte.apalache.io.itf.TlaToItfJson
import at.forsyte.apalache.io.json.ujsonimpl.{ScalaToUJsonAdapter, UJsonRepresentation}
import at.forsyte.apalache.tla.lir._

import java.io.PrintWriter

/**
 * This class produces counterexamples in the Informal Trace Format.
 *
 * @param writer
 *   a print writer to use
 * @author
 *   Igor Konnov
 */
class ItfCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {
  override def write(trace: Trace[TlaEx]): Unit = {
    writer.write(ujson.write(ItfCounterexampleWriter.mkJson(trace.module, trace.states), indent = 2))
  }
}

object ItfCounterexampleWriter {
  private val ujsonEncoder = new TlaToItfJson[UJsonRepresentation](ScalaToUJsonAdapter)

  /**
   * Produce a JSON representation of a counterexample in the ITF format
   *
   * @param rootModule
   *   the module that produced the counterexample
   * @param states
   *   a sequence of next states
   * @return
   *   the JSON representation of the counterexample in the ITF format
   */
  def mkJson(rootModule: TlaModule, states: IndexedSeq[Trace.State]): ujson.Value =
    ujsonEncoder.mkJson(rootModule, states).value

  def stateToJson(state: Trace.State, index: Int): ujson.Value =
    ujsonEncoder.stateToJson(state, index).value

  /**
   * Convert an individual TLA+ expression to its JSON representation in the ITF format.
   * @return
   *   a function that converts TLA+ expressions to JSON values
   */
  def exprToJson: TlaEx => ujson.Value = ex => ujsonEncoder.exprToJson(ex).value
}
