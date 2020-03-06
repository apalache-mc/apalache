package at.forsyte.apalache.tla.pp.passes

import java.io.{File, FileNotFoundException, FileReader}
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin, WriteablePassOptions}
import at.forsyte.apalache.io.tlc.TlcConfigParser
import at.forsyte.apalache.io.tlc.config._
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.pp.ConstAndDefRewriter
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.pp.TlcConfigImporter

/**
  * The pass that collects the configuration parameters and overrides constants and definitions.
  *
  * @param options pass options
  * @param nextPass next pass to call
  */
class ConfigurationPassImpl @Inject()(val options: PassOptions,
                                      tracker: TransformationTracker,
                                      @Named("AfterConfiguration") nextPass: Pass with TlaModuleMixin)
    extends ConfigurationPass with LazyLogging {

  private var outputTlaModule: Option[TlaModule] = None

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "ConfigurationPass"

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    var module = tlaModule.get

    // read TLC config if present
    val filename =
      options.getOrError("parser", "filename").asInstanceOf[String]
      .replaceFirst("\\.tla$", "\\.cfg")
    try {
      val config = TlcConfigParser.apply(new FileReader(filename))
      module = new TlcConfigImporter(config, new IdleTracker())(module)
      config.behaviorSpec match {
        case InitNextSpec(init, next) =>
          if(options.getOrElse("checker","init","").isEmpty) {
            options.asInstanceOf[WriteablePassOptions].set("checker.init", init)
          }
          else {
            logger.warn("Init operator is set both in " + filename + " and via CLI option --init; using the latter")
          }
          if(options.getOrElse("checker","next","").isEmpty) {
            options.asInstanceOf[WriteablePassOptions].set("checker.next", next)
          }
          else {
            logger.warn("Next operator is set both in " + filename + " and via CLI option --next; using the latter")
          }
        case _ => logger.warn("Temporal spec found in " + filename + ", which is not yet supported")
      }
      if(config.invariants.nonEmpty) {
        if(options.getOrElse("checker","inv",List()).isEmpty) {
          options.asInstanceOf[WriteablePassOptions].set("checker.inv", config.invariants)
        }
        else {
          logger.warn("Invariants are set both in " + filename + " and via CLI option --inv; using the latter")
        }

      }
    }
    catch {
      case _: FileNotFoundException => logger.info("No TLC configuration found; skipping")
      case e: TlcConfigParseError => logger.warn("Error parsing TLC configuration file: " + e.msg)
    }

    val rewritten = new ConstAndDefRewriter(tracker)(module)

    // dump the result of preprocessing
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(rewritten, new File(outdir.toFile, "out-config.tla"))

    outputTlaModule = Some(rewritten)
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    outputTlaModule map { m =>
      nextPass.setModule( m )
      nextPass
    }
  }
}
