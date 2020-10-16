package at.forsyte.apalache.tla.pp.passes

import java.io.{File, FileNotFoundException, FileReader}
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin, WriteablePassOptions}
import at.forsyte.apalache.io.tlc.TlcConfigParser
import at.forsyte.apalache.io.tlc.config._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaBoolOper, TlaTempOper, TlaOper}
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
    val currentModule = tlaModule.get
    // try to read from the TLC configuration file
    loadOptionsFromTlcConfig(currentModule)
    setFallbackOptions()

    // make sure that the required operators are defined
    ensureDeclarationsArePresent(currentModule)

    // rewrite constants and declarations
    val configuredModule = new ConstAndDefRewriter(tracker)(currentModule)

    // dump the configuration result
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(configuredModule, new File(outdir.toFile, "out-config.tla"))

    outputTlaModule = Some(configuredModule)
    true
  }

  // if checker.init and checker.next are not set, set them to Init and Next, respectively
  private def setFallbackOptions(): Unit = {
    if (options.get("checker", "init").isEmpty) {
      logger.info("  > Command line option --init is not set. Using Init")
      options.set("checker.init", "Init")
    }
    if (options.get("checker", "next").isEmpty) {
      logger.info("  > Command line option --next is not set. Using Next")
      options.set("checker.next", "Next")
    }
  }

  // set the configuration options from a TLC config, if it is present
  private def loadOptionsFromTlcConfig(module: TlaModule): Unit = {
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

    def setInit(init: String): Unit = {
      options.get[String]("checker","init") match {
        case None =>
          // In general, passes should not override options. This is a reasonable exception to this rule.
          logger.info(s"  > Using the init predicate $init from the TLC config")
          options.set("checker.init", init)

        case Some(cmdInit) =>
          logger.warn(s"  > $basename: Init operator is set in TLC config but overridden via --init command line option; using $cmdInit")
      }
    }

    def setNext(next: String): Unit = {
      options.get[String]("checker", "next") match {
        case None =>
          // In general, passes should not override options. This is a reasonable exception to this rule.
          logger.info(s"  > Using the next predicate $next from the TLC config")
          options.set("checker.next", next)

        case Some(cmdNext) =>
          val msg = s"  > $basename: Next operator is set in TLC config but overridden via --next command line option; using $cmdNext"
          logger.warn(msg)
      }
    }

    try {
      val config = TlcConfigParser.apply(new FileReader(filename))
      configuredModule = new TlcConfigImporter(config, new IdleTracker())(module)
      config.behaviorSpec match {
        case InitNextSpec(init, next) =>
          setInit(init)
          setNext(next)

        case TemporalSpec(specName) =>
          val (init, next) = extractFromSpec(module, basename, specName)
          logger.info(s"  > $basename: Using SPECIFICATION $specName")
          setInit(init)
          setNext(next)
      }
      if (config.invariants.nonEmpty) {
        logger.info(s"  > $basename: found INVARIANTS: " + String.join(", ", config.invariants :_*))

        options.get[List[String]]("checker", "inv") match {
          case None =>
            // In general, passes should not override options. This is a reasonable exception to this rule.
            options.set("checker.inv", config.invariants)

          case Some(cmdInvariants) =>
            val cmdInvariantsStr = cmdInvariants.map(s => "--inv " + s)
            logger.warn(s"  > Overriding with command line arguments: " + String.join(" ", cmdInvariantsStr :_*))
        }
      }

      if (config.temporalProps.nonEmpty) {
        // set the temporal properties, but warn the user that they are not used
        options.set("checker.temporalProps", config.temporalProps)
        for (prop <- config.temporalProps) {
          logger.warn(s"  > $basename: PROPERTY $prop is ignored. Only INVARIANTS are supported.")
        }
      }
    }
    catch {
      case _: FileNotFoundException =>
        if(configFilename.isEmpty) {
          logger.info("  > No TLC configuration found. Skipping.")
        }
        else {
          throw new TLCConfigurationError(s"  > $basename: TLC config is provided with --config, but not found")
        }
      case e: TlcConfigParseError =>
        throw new TLCConfigurationError(s"  > $basename:${e.pos}:  Error parsing the TLC config file: " + e.msg)
    }
  }

  // Make sure that all operators passed via --init, --cinit, --next, --inv are present.
  private def ensureDeclarationsArePresent(mod: TlaModule): Unit = {
    def assertDecl(role: String, name: String): Unit = {
      logger.info(s"  > Set $role to $name")
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

    options.get[List[String]]("checker", "temporalProps") match {
      case Some(props) =>
        props.foreach(assertDecl("a temporal property", _))

      case None =>
        () // this is fine, temporal properties are not supported anyway
    }
  }

  /**
    * Extract Init and Next from the spec definition that has the canonical form Init /\ [Next]_vars /\ ...
    * @param module TLA+ module
    * @param specName the name of the specification definition
    * @return the pair (Init, Next)
    */
  private def extractFromSpec(module: TlaModule, contextName: String, specName: String): (String, String) = {
    module.operDeclarations.find(_.name == specName) match {
      case None =>
        throw new ConfigurationError(s"$contextName: Operator $specName not found (used as SPECIFICATION)")

        // the canonical form: Init /\ [][Next]_vars /\ ...
      case Some(TlaOperDecl(_, List(),
        OperEx(TlaBoolOper.and,
          // Init
          OperEx(TlaOper.apply, NameEx(init)),
          // [][Next]_vars
          OperEx(TlaTempOper.box,
            // [Next]_vars
            OperEx(TlaActionOper.stutter,
              // Next
              OperEx(TlaOper.apply, NameEx(next)),
              // vars
            _*
          )), ///
          _*))) =>
        (init, next)

      case Some(d) =>
        logger.error(s"Operator $specName of ${d.formalParams.length} arguments is defined as: " + d.body)
        val msg = s"$contextName: Expected $specName to be in the canonical form Init /\\ [][Next]_vars /\\ ..."
        throw new ConfigurationError(msg)
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
