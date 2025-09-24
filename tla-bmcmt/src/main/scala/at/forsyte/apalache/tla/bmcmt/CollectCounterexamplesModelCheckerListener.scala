package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.lir.Trace
import at.forsyte.apalache.tla.lir.TlaEx
import com.typesafe.scalalogging.LazyLogging

import scala.collection.mutable.ListBuffer

/**
 * Observer to [[SeqModelChecker]] that collects all counterexamples in [[counterExamples]].
 */
class CollectCounterexamplesModelCheckerListener extends ModelCheckerListener with LazyLogging {

  override def onCounterexample(
      counterexample: Trace[TlaEx],
      errorIndex: Int): Unit = {
    _counterExamples += counterexample
  }

  override def onExample(counterexample: Trace[Unit], exampleIndex: Int): Unit = {
    // ignore the examples
  }

  private val _counterExamples = ListBuffer.empty[Trace[TlaEx]]

  def counterExamples: Seq[Trace[TlaEx]] = _counterExamples.toSeq
}
