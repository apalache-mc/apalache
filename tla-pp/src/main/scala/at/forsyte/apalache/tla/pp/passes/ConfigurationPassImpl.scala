package at.forsyte.apalache.tla.pp.passes

import java.io.{File, FileNotFoundException, FileReader}
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin, WriteablePassOptions}
import at.forsyte.apalache.io.tlc.TlcConfigParser
import at.forsyte.apalache.io.tlc.config._
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.pp._
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging
import org.apache.commons.io.FilenameUtils

/**
  * The pass that collects the configuration parameters and overrides constants and definitions.
  * This pass also overrides attributes in the PassOptions object:
  * checker.init, checker.next, checker.cinit, checker.inv. In general, passes should not override options.
  * This is a reasonable exception to this rule, as this pass configures the options based on the user input.
  *
  * @param options pass options
  * @param nextPass next pass to call
  */
class ConfigurationPassImpl @Inject()(val options: WriteablePassOptions,
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
    // try to read from the TLC configuration file
    val configuredModule = tryConfigureFromTlcConfig(tlaModule.get)

    // dump the configuration result
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(configuredModule, new File(outdir.toFile, "out-config.tla"))

    setFallbackOptions()

    // make sure that the required operators are defined
    ensureDeclarationsArePresent(configuredModule)

    outputTlaModule = Some(configuredModule)
    true
  }

  // if checker.init and checker.next are not set, set them to Init and Next, respectively
  private def setFallbackOptions(): Unit = {
    if (options.get("checker", "init").isEmpty) {
      logger.debug("  > Option --init is not set. Using Init")
      options.set("checker.init", "Init")
    }
    if (options.get("checker", "next").isEmpty) {
      logger.debug("  > Option --next is not set. Using Next")
      options.set("checker.next", "Next")
    }
  }

  // set the configuration options from a TLC config, if it is present
  private def tryConfigureFromTlcConfig(module: TlaModule): TlaModule = {
    var configuredModule = module
    // read TLC config if present
    val configFilename = options.getOrElse("checker","config","")
    val filename =
      if(configFilename.isEmpty)
        options.getOrError("parser", "filename").asInstanceOf[String]
          .replaceFirst("\\.(tla|json)$", "\\.cfg")
      else
        configFilename
    val basename = FilenameUtils.getName(filename)
    logger.info("  > Loading TLC configuration from " + basename)
    try {
      val config = TlcConfigParser.apply(new FileReader(filename))
      configuredModule = new TlcConfigImporter(config, new IdleTracker())(module)
      config.behaviorSpec match {
        case InitNextSpec(init, next) =>
          if(options.getOrElse("checker","init","").isEmpty) {
            options.set("checker.init", init)
          }
          else {
            logger.warn("  > Init operator is set both in " + basename + " and via --init option; using the latter")
          }
          if(options.getOrElse("checker","next","").isEmpty) {
            // In general, passes should not override options. This is a reasonable exception to this rule.
            options.set("checker.next", next)
          }
          else {
            logger.warn("  > Next operator is set both in " + basename + " and via --next option; using the latter")
          }
        case _ => logger.warn("  > Temporal spec found in " + basename + ", which is not yet supported. Skipping.")
      }
      if(config.invariants.nonEmpty) {
        if(options.getOrElse("checker","inv",List()).isEmpty) {
          // In general, passes should not override options. This is a reasonable exception to this rule.
          options.set("checker.inv", config.invariants)
        }
        else {
          logger.warn("  > Invariants are set both in " + basename + " and via --inv option; using the latter")
        }

      }
    }
    catch {
      case _: FileNotFoundException =>
        if(configFilename.isEmpty) {
          logger.info("  > No TLC configuration found. Skipping.")
        }
        else {
          throw new TLCConfigurationError("  > Could not find TLC config file " + basename + " given via --config option")
        }
      case e: TlcConfigParseError =>
        throw new TLCConfigurationError("  > Could not parse TLC configuration in " + basename + ": " + e.msg)
    }

    // rewrite constants and declarations
    new ConstAndDefRewriter(tracker)(configuredModule)
  }

  // Make sure that all operators passed via --init, --cinit, --next, --inv are present.
  private def ensureDeclarationsArePresent(mod: TlaModule): Unit = {
    def assertDecl(role: String, name: String): Unit = {
      if (mod.operDeclarations.forall(_.name != name)) {
        throw new ConfigurationError(s"Operator $name not found (used as $role)")
      }
    }

    // let's make this code as fool-proof as possible, so the following passes do not fail with exceptions
    options.get[String]("checker", "init") match {
      case Some(init) => assertDecl("the initialization predicate", init)

      case None =>
        throw new IrrecoverablePreprocessingError("Option checker.init not set")
    }

    options.get[String]("checker", "cinit") match {
      case Some(cinit) => assertDecl("the constant initialization predicate", cinit)

      case None => () // cinit is optional
    }

    options.get[String]("checker", "next") match {
      case Some(next) => assertDecl("the transition predicate", next)

      case None =>
        throw new IrrecoverablePreprocessingError("Option checker.next not set")
    }

    options.get[List[String]]("checker", "inv") match {
      case Some(invs) =>
        invs.foreach(assertDecl("an invariant", _))

      case None =>
        () // this is fine, invariants are optional
    }
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
