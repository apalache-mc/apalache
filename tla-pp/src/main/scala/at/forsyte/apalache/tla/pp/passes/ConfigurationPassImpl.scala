package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin, WriteablePassOptions}
import at.forsyte.apalache.io.tlc.TlcConfigParserApalache
import at.forsyte.apalache.io.tlc.config._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.io.lir.{PrettyWriter, TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaBoolOper, TlaOper, TlaTempOper}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.pp._
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging
import org.apache.commons.io.FilenameUtils

import java.io.{File, FileNotFoundException, FileReader}
import java.nio.file.Path

/**
 * The pass that collects the configuration parameters and overrides constants and definitions.
 * This pass also overrides attributes in the PassOptions object:
 * checker.init, checker.next, checker.cinit, checker.inv. In general, passes should not override options.
 * This is a reasonable exception to this rule, as this pass configures the options based on the user input.
 *
 * @param options  pass options
 * @param nextPass next pass to call
 */
class ConfigurationPassImpl @Inject() (
    val options: WriteablePassOptions, tracker: TransformationTracker, writerFactory: TlaWriterFactory,
    @Named("AfterConfiguration") nextPass: Pass with TlaModuleMixin
) extends ConfigurationPass with LazyLogging {

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
    // this pass is hard to read, too many things are happening here...
    val currentModule = tlaModule.get
    val relevantOptions = new WriteablePassOptions()
    copyRelevantOptions(options, relevantOptions)
    // try to read from the TLC configuration file and produce constant overrides
    val overrides = loadOptionsFromTlcConfig(currentModule, relevantOptions)
    val currentAndOverrides =
      new TlaModule(currentModule.name, currentModule.declarations ++ overrides)
    setFallbackOptions(relevantOptions)

    // make sure that the required operators are defined
    ensureDeclarationsArePresent(currentAndOverrides, relevantOptions)

    // copy the relevant options back in options
    copyRelevantOptions(relevantOptions, options)

    // rewrite constants and declarations
    val configuredModule = new ConstAndDefRewriter(tracker)(currentAndOverrides)
    // Igor: I thought of rewriting all definitions in NormalizedNames.OPTION_NAMES into normalized names.
    // However, that should be done very carefully. Maybe we should do that in the future.

    // dump the configuration result
    writerFactory.writeModuleAllFormats(configuredModule.copy(name = "02_OutConfig"), TlaWriter.STANDARD_MODULES)

    outputTlaModule = Some(configuredModule)
    true
  }

  // if checker.init and checker.next are not set, set them to Init and Next, respectively
  private def setFallbackOptions(
      relevantOptions: WriteablePassOptions
  ): Unit = {
    if (relevantOptions.get("checker", "init").isEmpty) {
      logger.info("  > Command line option --init is not set. Using Init")
      relevantOptions.set("checker.init", "Init")
    }
    if (relevantOptions.get("checker", "next").isEmpty) {
      logger.info("  > Command line option --next is not set. Using Next")
      relevantOptions.set("checker.next", "Next")
    }
  }

  // copy the relevant options
  private def copyRelevantOptions(
      from: PassOptions, to: WriteablePassOptions
  ): Unit = {
    for (name <- NormalizedNames.STANDARD_OPTION_NAMES) {
      from
        .get[Any]("checker", name)
        .collect { case value => to.set("checker." + name, value) }
    }
  }

  /**
   * Produce the configuration options from a TLC config, if it is present.
   *
   * @param module     the input module
   * @param outOptions the pass options to update from the configuration file
   * @return additional declarations, which originate from assignments and replacements
   */
  private def loadOptionsFromTlcConfig(
      module: TlaModule, outOptions: WriteablePassOptions
  ): Seq[TlaDecl] = {
    var configuredModule = module
    // read TLC config if present
    val configFilename = options.getOrElse("checker", "config", "")
    val filename =
      if (configFilename.isEmpty) {
        options
          .getOrError("parser", "filename")
          .asInstanceOf[String]
          .replaceFirst("\\.(tla|json)$", "\\.cfg")
      } else {
        configFilename
      }
    val basename = FilenameUtils.getName(filename)
    logger.info(s"  > $basename: Loading TLC configuration")

    def setInit(init: String): Unit = {
      outOptions.get[String]("checker", "init") match {
        case None =>
          logger.info(s"  > Using the init predicate $init from the TLC config")
          outOptions.set("checker.init", init)

        case Some(cmdInit) =>
          logger.warn(
              s"  > $basename: Init operator is set in TLC config but overridden via --init command line option; using $cmdInit"
          )
          outOptions.set("checker.init", cmdInit)
      }
    }

    def setNext(next: String): Unit = {
      outOptions.get[String]("checker", "next") match {
        case None =>
          logger.info(s"  > Using the next predicate $next from the TLC config")
          outOptions.set("checker.next", next)

        case Some(cmdNext) =>
          val msg =
            s"  > $basename: Next operator is set in TLC config but overridden via --next command line option; using $cmdNext"
          logger.warn(msg)
          outOptions.set("checker.next", cmdNext)
      }
    }

    try {
      val config = TlcConfigParserApalache.apply(new FileReader(filename))
      configuredModule = new TlcConfigImporter(config, new IdleTracker())(
          module
      )
      config.behaviorSpec match {
        case InitNextSpec(init, next) =>
          setInit(init)
          setNext(next)

        case TemporalSpec(specName) =>
          val (init, next) = extractFromSpec(module, basename, specName)
          logger.info(s"  > $basename: Using SPECIFICATION $specName")
          setInit(init)
          setNext(next)

        case NullSpec() =>
          () // do nothing
      }
      if (config.invariants.nonEmpty) {
        logger.info(
            s"  > $basename: found INVARIANTS: " + String.join(
                ", ",
                config.invariants: _*
            )
        )

        outOptions.get[List[String]]("checker", "inv") match {
          case None =>
            outOptions.set("checker.inv", config.invariants)

          case Some(cmdInvariants) =>
            val cmdInvariantsStr = cmdInvariants.map(s => "--inv " + s)
            logger.warn(
                s"  > Overriding with command line arguments: " + String.join(
                    " ",
                    cmdInvariantsStr: _*
                )
            )
            outOptions.set("checker.inv", cmdInvariants)
        }
      }

      if (config.temporalProps.nonEmpty) {
        // set the temporal properties, but warn the user that they are not used
        outOptions.set("checker.temporalProps", config.temporalProps)
        for (prop <- config.temporalProps) {
          logger.warn(
              s"  > $basename: PROPERTY $prop is ignored. Only INVARIANTS are supported."
          )
        }
      }

      val namesOfOverrides =
        (config.constAssignments.keySet ++ config.constReplacements.keySet)
          .map(ConstAndDefRewriter.OVERRIDE_PREFIX + _)
      configuredModule.declarations.filter(d => namesOfOverrides.contains(d.name))
    } catch {
      case _: FileNotFoundException =>
        if (configFilename.isEmpty) {
          logger.info("  > No TLC configuration found. Skipping.")
          List()
        } else {
          throw new TLCConfigurationError(
              s"  > $basename: TLC config is provided with --config, but not found"
          )
        }

      case e: TlcConfigParseError =>
        throw new TLCConfigurationError(
            s"  > $basename:${e.pos}:  Error parsing the TLC config file: " + e.msg
        )
    }
  }

  // Make sure that all operators passed via --init, --cinit, --next, --inv are present.
  private def ensureDeclarationsArePresent(
      mod: TlaModule, configOptions: PassOptions
  ): Unit = {
    def assertDecl(role: String, name: String): Unit = {
      logger.info(s"  > Set $role to $name")
      if (mod.operDeclarations.forall(_.name != name)) {
        throw new ConfigurationError(
            s"Operator $name not found (used as $role)"
        )
      }
    }

    // let's make this code as fool-proof as possible, so the following passes do not fail with exceptions
    configOptions.get[String]("checker", "init") match {
      case Some(init) => assertDecl("the initialization predicate", init)

      case None =>
        throw new IrrecoverablePreprocessingError("Option checker.init not set")
    }

    configOptions.get[String]("checker", "cinit") match {
      case Some(cinit) =>
        assertDecl("the constant initialization predicate", cinit)

      case None => () // cinit is optional
    }

    configOptions.get[String]("checker", "next") match {
      case Some(next) => assertDecl("the transition predicate", next)

      case None =>
        throw new IrrecoverablePreprocessingError("Option checker.next not set")
    }

    configOptions.get[List[String]]("checker", "inv") match {
      case Some(invs) =>
        invs.foreach(assertDecl("an invariant", _))

      case None =>
        () // this is fine, invariants are optional
    }

    configOptions.get[List[String]]("checker", "temporalProps") match {
      case Some(props) =>
        props.foreach(assertDecl("a temporal property", _))

      case None =>
        () // this is fine, temporal properties are not supported anyway
    }
  }

  /**
   * Extract Init and Next from the spec definition that has the canonical form Init /\ [Next]_vars /\ ...
   *
   * @param module   TLA+ module
   * @param specName the name of the specification definition
   * @return the pair (Init, Next)
   */
  private def extractFromSpec(
      module: TlaModule, contextName: String, specName: String
  ): (String, String) = {
    // flatten nested conjunctions into a single one
    def flattenAnds: TlaEx => TlaEx = {
      case OperEx(TlaBoolOper.and, args @ _*) =>
        val flattenedArgs = args map flattenAnds
        val (ands, nonAnds) = flattenedArgs.partition {
          case OperEx(TlaBoolOper.and, _*) => true
          case _                           => false
        }
        val propagated = ands.collect { case OperEx(TlaBoolOper.and, as @ _*) =>
          as
        }.flatten
        OperEx(TlaBoolOper.and, propagated ++ nonAnds: _*)

      case ex @ _ => ex
    }

    def throwError(d: TlaOperDecl): Nothing = {
      logger.error(
          s"Operator $specName of ${d.formalParams.length} arguments is defined as: " + d.body
      )
      val msg =
        s"$contextName: Expected $specName to be in the canonical form Init /\\ [][Next]_vars /\\ ..."
      throw new ConfigurationError(msg)
    }

    module.operDeclarations.find(_.name == specName) match {
      case None =>
        throw new ConfigurationError(
            s"$contextName: Operator $specName not found (used as SPECIFICATION)"
        )

      // the canonical form: Init /\ [][Next]_vars /\ ...
      case Some(decl @ TlaOperDecl(_, List(), spec)) =>
        flattenAnds(spec) match {
          case OperEx(TlaBoolOper.and, args @ _*) =>
            val (nonFairness, fairness) = args.partition {
              case OperEx(TlaTempOper.weakFairness, _*)   => false
              case OperEx(TlaTempOper.strongFairness, _*) => false
              case _                                      => true
            }
            val (init, next) =
              nonFairness match {
                case Seq(
                        OperEx(TlaOper.apply, NameEx(init)), // Init
                        OperEx(
                            TlaTempOper.box,
                            OperEx(
                                TlaActionOper.stutter,
                                OperEx(TlaOper.apply, NameEx(next)),
                                _*
                            )
                        ) // [][Next]_vars
                    ) =>
                  (init, next)

                case Seq(
                        OperEx(
                            TlaTempOper.box,
                            OperEx(
                                TlaActionOper.stutter,
                                OperEx(TlaOper.apply, NameEx(next)),
                                _*
                            )
                        ),
                        OperEx(TlaOper.apply, NameEx(init)) // Init
                    ) =>
                  (init, next)

                case _ => throwError(decl)
              }

            if (fairness.nonEmpty) {
              val es = fairness.mkString(" /\\ ")
              val msg = s"Fairness constraints are ignored by Apalache: $es"
              logger.warn(msg)
            }

            (init, next)
        }

      case Some(d) =>
        throwError(d)
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
      nextPass.setModule(m)
      nextPass
    }
  }
}
