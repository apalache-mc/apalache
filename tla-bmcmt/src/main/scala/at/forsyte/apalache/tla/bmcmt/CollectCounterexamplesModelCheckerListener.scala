package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution
import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}
import com.typesafe.scalalogging.LazyLogging

import scala.collection.mutable.ListBuffer

/**
 * Observer to [[SeqModelChecker]] that collects all counterexamples in [[counterExamples]].
 */
class CollectCounterexamplesModelCheckerListener extends ModelCheckerListener with LazyLogging {

  override def onCounterexample(
      rootModule: TlaModule,
      trace: DecodedExecution,
      invViolated: TlaEx,
      errorIndex: Int): Unit = {
    _counterExamples += trace
  }

  override def onExample(rootModule: TlaModule, trace: DecodedExecution, exampleIndex: Int): Unit = {
    // ignore the examples
  }

  private val _counterExamples = ListBuffer.empty[DecodedExecution]

  def counterExamples: Seq[DecodedExecution] = _counterExamples.toSeq
}
