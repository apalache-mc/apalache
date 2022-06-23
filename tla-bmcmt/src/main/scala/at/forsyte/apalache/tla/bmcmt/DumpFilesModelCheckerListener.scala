package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.lir.CounterexampleWriter
import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{BoolT1, TlaEx, TlaModule}
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.storage.NameReplacementMap

/**
 * Observer to [[SeqModelChecker]] that dumps example and counterexample traces to files.
 *
 * The traces are written to files
 *   - `${prefix}${index}.{tla,json,.itf.json}` contains the current (counter)example
 *   - `${prefix}.{tla,json,.itf.json}` contains the latest (counter)example
 *
 * where $prefix and $index are
 *   - "violation" and `errorIndex` for counterexamples, and
 *   - "example" and `exampleIndex` for examples.
 */
object DumpFilesModelCheckerListener extends ModelCheckerListener with LazyLogging {

  override def onCounterexample(
      rootModule: TlaModule,
      trace: DecodedExecution,
      invViolated: TlaEx,
      errorIndex: Int,
      nameReplacementMap: NameReplacementMap): Unit = {
    dump(rootModule, trace, invViolated, errorIndex, "violation", nameReplacementMap)
  }

  override def onExample(
      rootModule: TlaModule,
      trace: DecodedExecution,
      exampleIndex: Int,
      nameReplacementMap: NameReplacementMap): Unit = {
    dump(rootModule, trace, tla.bool(true).as(BoolT1), exampleIndex, "example", nameReplacementMap)
  }

  private def dump(
      rootModule: TlaModule,
      trace: DecodedExecution,
      invViolated: TlaEx,
      index: Int,
      prefix: String,
      nameReplacementMap: NameReplacementMap): Unit = {
    val states = trace.path.map(p => (p._2.toString, p._1))

    def dump(suffix: String): List[String] = {
      CounterexampleWriter.writeAllFormats(prefix, suffix, rootModule, invViolated, states, nameReplacementMap)
    }

    // for a human user, write the latest (counter)example into ${prefix}.{tla,json,...}
    dump("")

    // for automation scripts, produce ${prefix}${index}.{tla,json,...}
    val filenames = dump(index.toString)

    logger.error(s"Check the trace in: ${filenames.mkString(", ")}")
  }
}
