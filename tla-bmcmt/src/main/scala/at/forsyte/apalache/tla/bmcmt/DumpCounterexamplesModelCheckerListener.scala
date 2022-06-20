package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.lir.CounterexampleWriter
import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{BoolT1, TlaEx, TlaModule}
import com.typesafe.scalalogging.LazyLogging

/**
 * Observer to [[SeqModelChecker]] that dumps counterexamples to files.
 */
object DumpCounterexamplesModelCheckerListener extends ModelCheckerListener with LazyLogging {

  override def onCounterexample(
      rootModule: TlaModule,
      trace: DecodedExecution,
      invViolated: TlaEx,
      errorIndex: Int): Unit = {
    dump(rootModule, trace, invViolated, errorIndex, "violation")
  }

  override def onExample(rootModule: TlaModule, trace: DecodedExecution, exampleIndex: Int): Unit = {
    dump(rootModule, trace, tla.bool(true).as(BoolT1), exampleIndex, "example")
  }

  private def dump(
      rootModule: TlaModule,
      trace: DecodedExecution,
      invViolated: TlaEx,
      index: Int,
      prefix: String): Unit = {
    val states = trace.path.map(p => (p._2.toString, p._1))

    def dump(suffix: String): List[String] = {
      CounterexampleWriter.writeAllFormats(prefix, suffix, rootModule, invViolated, states)
    }

    // for a human user, write the latest counterexample into counterexample.{tla,json}
    dump("")

    // for automation scripts, produce counterexample${nFoundErrors}.{tla,json}
    val filenames = dump(index.toString)

    logger.error(s"Check the trace in: ${filenames.mkString(", ")}")
  }
}
