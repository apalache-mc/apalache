package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution
import at.forsyte.apalache.tla.lir.TlaModule
import com.typesafe.scalalogging.LazyLogging

import scala.collection.mutable.ListBuffer

/**
 * Observer to [[SeqModelChecker]] that collects all counterexamples in [[counterExamples]].
 */
class CollectCounterexamplesModelCheckerListener extends ModelCheckerListener with LazyLogging {

  override def onCounterexample(
      counterexample: Counterexample,
      errorIndex: Int): Unit = {
    _counterExamples += counterexample
  }

  override def onExample(rootModule: TlaModule, trace: DecodedExecution, exampleIndex: Int): Unit = {
    // ignore the examples
  }

  private val _counterExamples = ListBuffer.empty[Counterexample]

  def counterExamples: Seq[Counterexample] = _counterExamples.toSeq
}
