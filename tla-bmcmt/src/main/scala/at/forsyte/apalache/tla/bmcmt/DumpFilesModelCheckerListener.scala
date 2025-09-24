package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.lir.{CounterexampleWriter, Trace}
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{BoolT1, TlaEx}
import com.typesafe.scalalogging.LazyLogging

/**
 * Observer to [[SeqModelChecker]] that dumps example and counterexample traces to files.
 *
 * The traces are written to files
 *   - `\${prefix}\${index}.{tla,json,.itf.json}` contains the current (counter)example
 *   - `\${prefix}.{tla,json,.itf.json}` contains the latest (counter)example
 *
 * where \$prefix and \$index are
 *   - "violation" and `errorIndex` for counterexamples, and
 *   - "example" and `exampleIndex` for examples.
 */
object DumpFilesModelCheckerListener extends ModelCheckerListener with LazyLogging {

  override def onCounterexample(counterexample: Trace[TlaEx], errorIndex: Int): Unit = {
    dump(counterexample, errorIndex, "violation")
  }

  override def onExample(counterexample: Trace[Unit], exampleIndex: Int): Unit = {
    dump(counterexample.copy[TlaEx](data = tla.bool(true).as(BoolT1)), exampleIndex, "example")
  }

  private def dump(
      counterexample: Trace[TlaEx],
      index: Int,
      prefix: String): Unit = {
    def dump(suffix: String): List[String] = {
      // TODO(shonfeder): Should the CounterexampleWriter take a Counterexample?
      // Would require fixing inter-package dependencies, since it would require
      // exposing the Counterexample class to the tla-io project.
      CounterexampleWriter.writeAllFormats(
          prefix,
          suffix,
          counterexample,
      )
    }

    // for a human user, write the latest (counter)example into ${prefix}.{tla,json,...}
    dump("")

    // for automation scripts, produce ${prefix}${index}.{tla,json,...}
    val filenames = dump(index.toString)

    logger.info(s"Check the trace in: ${filenames.mkString(", ")}")
  }
}
