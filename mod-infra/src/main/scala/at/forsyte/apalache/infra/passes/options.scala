package at.forsyte.apalache.infra.passes.options

import at.forsyte.apalache.infra.PassOptionException
import at.forsyte.apalache.infra.tlc.TlcConfigParserApalache
import at.forsyte.apalache.infra.tlc.config.{BehaviorSpec, InitNextSpec, TlcConfig, TlcConfigParseError}
import at.forsyte.apalache.tla.lir.Feature
import com.typesafe.scalalogging.LazyLogging
import org.apache.commons.io.FilenameUtils

import java.io.{File, FileReader, IOException}
import scala.util.{Failure, Success, Try}

/**
 * The components of this package specify the configurations and options used to configure Apalache
 *
 * Configurations are represented by extension of the [[Config]] trait. Configurations are derived via injective maps
 * from configuration sources (souch as CLI arguments or .cfg files) to instances of [[Config]]. As such, each value in
 * an extension of [[Config]] should be an `Option`, where a value of `None` indicates that value was left unconfigured.
 *
 * Options are represented by extensions of the [[OptionGroup]] trait. Option groups are typically derived via
 * surjective maps from from [[Config]]s to instances of [[OptionGroup]]. As such, for every field in the option group,
 * there must be a value given in the originating config.
 *
 * The aforementioned maps can be defined in any number of ways, via methods on a companion object, by using
 * `PureConfig` for automatic derivation (see, e.g. 'apalache.io.ConfigManager'), or via arbitrary functions.
 *
 * See
 * [[https://github.com/informalsystems/apalache/blob/main/docs/src/adr/022adr-unification-of-configs-and-options.md ADR022]]
 * for motivation and details.
 *
 * @author
 *   Shon Feder
 */

/**
 * The basic interface of classes that specify application configurations
 *
 * Each subclass of `Config` is a case class that specifies a set of related configurations, which we refer to as a
 * "config group".
 */
sealed trait Config[T] {

  /**
   * Produces a copy of the config group `T` with all its attributes (and all the attributes of possibly nested config
   * groups) set to `None`
   */
  def empty: T
}

/**
 * Specifies the program configuration for Apalache
 *
 * The case classes extending `Config` aim to specify the entirety of Apalache's configurable values, along with their
 * defaults. Each case class specifies a group of related configuration values.
 *
 * Each subclass `T` of [[Config]][T] should have the following properties:
 *
 *   - Each case class' arguments should either be a ''configurable value'' or a child configuration group of type
 *     `Config[U]`.
 *   - Each configurable value should be of type `Option[T]`, wherein `None` indicates the configuration source has
 *     omitted the value and `Some(v)` sets the value to `v`.
 */
object Config {

  // We use shapeless to derive empty values of the configs generically, without
  // having to manually set each field.
  import shapeless._

  // Constructs a higher-ranked function that can map HLists of config values that can be made "empty"
  private object emptyPoly extends Poly1 {
    // Takes a `v : Option[T]` to `None : Option[T]`
    implicit def noneCase[T]: Case.Aux[Option[T], Option[T]] = at(o => o.flatMap(_ => None))
    // Takes a `Config[T]` to an empty version of the config (with all fields set to `None`)
    implicit def configCase[T <: Config[T]]: Case.Aux[T, T] = at(cfg => cfg.empty)
  }

  /**
   * The common configurations shared by all of Apalache's modes of execution
   *
   * @param command
   *   The subcommand or process being executed
   * @param inputfile
   *   The file from which input data can be read
   * @param outDir
   *   An additional directory wherein logging and diagnostic outputs for this run will be written (in addition to a run
   *   directory inside the `outDir`)
   * @param runDir
   *   A directory into which logging and diagnostic outputs for the latest run will be written (in addition to the
   *   run-dirs accumulated in the `outDir`)
   * @param debug
   *   Whether or not to enable debug level output
   * @param smtprof
   *   Whether or not to write SMT profiling into the `runDir`
   * @param configFile
   *   A file from which a local configuration is to be read
   * @param writeIntermediate
   *   Whether or not to write intermediate data into the `runDir`
   * @param profiling
   *   Whether or not to write general profiling data into the `runDir`
   * @param features
   *   Control experimental features
   */
  case class Common(
      command: Option[String] = None,
      outDir: Option[File] = Some(new File(System.getProperty("user.dir"), "_apalache-out")),
      runDir: Option[File] = None,
      debug: Option[Boolean] = Some(false),
      smtprof: Option[Boolean] = Some(false),
      configFile: Option[File] = None,
      writeIntermediate: Option[Boolean] = Some(false),
      profiling: Option[Boolean] = Some(false),
      features: Option[Seq[Feature]] = Some(Seq()))
      extends Config[Common] {

    def empty: Common = Generic[Common].from(Generic[Common].to(this).map(emptyPoly))
  }

  /**
   * Configuration of program input
   *
   * @param source
   *   SourceOption from which input data can be read
   */
  case class Input(source: Option[SourceOption] = None) extends Config[Input] {

    def empty: Input = Generic[Input].from(Generic[Input].to(this).map(emptyPoly))
  }

  /**
   * Configuration of program output
   *
   * @param output
   *   File into which output data is to be written
   */
  case class Output(output: Option[File] = None) extends Config[Output] {

    def empty: Output = Generic[Output].from(Generic[Output].to(this).map(emptyPoly))
  }

  /**
   * Configuration of model checking
   *
   * @param tuning
   *   A map of various settings to alter the model checking behavior
   * @param algo
   *   the search algorithm: offline, incremental, parallel (soon), default: incremental
   * @param config
   *   location of a configuration file in TLC format
   * @param cinit
   *   the name of an operator that initializes CONSTANTS
   * @param discardDisabled
   *   pre-check whether a transition is disabled, and discard it, to make SMT queries smaller
   * @param init
   *   the name of an operator that initializes VARIABLES
   * @param inv
   *   the names of invariant operators
   * @param next
   *   the name of a transition operator
   * @param length
   *   maximal number of Next steps
   * @param maxError
   *   whether to stop on the first error or to produce up to a given number of counterexamples
   * @param noDeadLocks
   *   do not check for deadlocks
   * @param nworkers
   *   the number of workers for the parallel checker (not currently used)
   * @param smtEncoding
   *   the SMT encoding to use
   * @param temporalProps
   *   the names of temporal properties
   * @param view
   *   the state view to use for generating counter examples when `maxError` is set
   */
  case class Checker(
      tuning: Option[Map[String, String]] = Some(Map()),
      algo: Option[Algorithm] = Some(Algorithm.Incremental),
      config: Option[File] = None,
      discardDisabled: Option[Boolean] = Some(true),
      cinit: Option[String] = None,
      init: Option[String] = None,
      inv: Option[List[String]] = None,
      next: Option[String] = None,
      length: Option[Int] = Some(10),
      maxError: Option[Int] = Some(1),
      noDeadlocks: Option[Boolean] = Some(false),
      nworkers: Option[Int] = Some(1),
      smtEncoding: Option[SMTEncoding] = Some(SMTEncoding.OOPSLA19),
      temporalProps: Option[List[String]] = None,
      view: Option[String] = None)
      extends Config[Checker] {

    def empty: Checker = Generic[Checker].from(Generic[Checker].to(this).map(emptyPoly))

    // The following helper methods record default values for derived
    // specification predicates, that will need to be computed after parsing a
    // TLC config file. Since values set by CLI and apalache.cfg override
    // subsequently derived parameters, we need to track whether or not the
    // value was set when we go to parse out a TLC cfg file.

    def initOrDefault = init.getOrElse("Init")
    def nextOrDefault = next.getOrElse("Next")
    def invOrDefault = inv.getOrElse(List.empty)
    def temporalPropsOrDefault = temporalProps.getOrElse(List.empty)
  }

  /**
   * Configuration of trace evaluation
   *
   * @param trace
   *   an ITF trace file
   * @param expressions
   *   a list of expressions, to be evaluated at every state in the trace
   */
  case class Tracee(
      trace: Option[SourceOption] = None,
      expressions: Option[List[String]] = None)
      extends Config[Tracee] {

    def empty: Tracee = Generic[Tracee].from(Generic[Tracee].to(this).map(emptyPoly))
  }

  /**
   * Configuration of type checking
   *
   * @param inferpoly
   *   allow the type checker to infer polymorphic types
   */
  case class Typechecker(
      inferpoly: Option[Boolean] = Some(true))
      extends Config[Typechecker] {

    def empty: Typechecker = Generic[Typechecker].from(Generic[Typechecker].to(this).map(emptyPoly))
  }

  /**
   * Configuration of the server
   *
   * @param port
   *   the port to serve requests from
   */
  case class Server(
      port: Option[Int] = Some(8822))
      extends Config[Server] {

    def empty: Server = Generic[Server].from(Generic[Server].to(this).map(emptyPoly))
  }

  /**
   * The complete configuration
   *
   * Gathers all configuration groups
   */
  case class ApalacheConfig(
      common: Common = Common(),
      input: Input = Input(),
      output: Output = Output(),
      checker: Checker = Checker(),
      typechecker: Typechecker = Typechecker(),
      tracee: Tracee = Tracee(),
      server: Server = Server())
      extends Config[ApalacheConfig] {

    def empty: ApalacheConfig = Generic[ApalacheConfig].from(Generic[ApalacheConfig].to(this).map(emptyPoly))
  }
}

/** Defines the data sources supported */
sealed abstract class SourceOption {

  def isFile: Boolean

  def exists: Boolean

  def format: SourceOption.Format

  def toString: String

  /**
   * Derive a source, and possibly a sequence of auxiliary sources, from the content of the `SourceOption`
   *
   * The pair returned is essentially just a lightweight representation of a non-empty sequence
   */
  def toSources: (scala.io.Source, Seq[scala.io.Source])

}

object SourceOption {
  import scala.io.Source

  /** The format used to represent the source's content */
  sealed abstract class Format {}
  object Format {
    case object Tla extends Format
    case object Json extends Format
    case object Itf extends Format
  }

  /** Data to be loaded from a file */
  final case class FileSource(file: java.io.File, format: Format) extends SourceOption {
    def isFile = true
    def exists = file.exists()
    def toSources = (Source.fromFile(file), Seq())

    override def toString = file.toString()
  }

  object FileSource {

    private def hasItfSubExtension(fname: String): Boolean =
      FilenameUtils.isExtension(FilenameUtils.removeExtension(fname), "itf")

    /** Create a FileSource from a file, deriving the format from the file's extension */
    def apply(file: java.io.File): FileSource = {
      val fname = file.getName()
      val format = FilenameUtils.getExtension(fname) match {
        case "tla"                               => Format.Tla
        case "json" if hasItfSubExtension(fname) => Format.Itf
        case "json"                              => Format.Json
        case unknown                             => throw new PassOptionException(s"Unsupported file format ${unknown}")
      }
      new FileSource(file, format)
    }
  }

  /**
   * Data supplied as a string
   *
   * @param content
   *   the principle data source
   * @param aux
   *   auxiliary data sources
   */
  final case class StringSource(content: String, aux: Seq[String] = Seq(), format: Format = Format.Tla)
      extends SourceOption {
    def isFile = false
    def exists = true
    def toSources = (Source.fromString(content), aux.map(Source.fromString(_)))

    override def toString = s"StringSource(${format})"
  }
}

/** Defines the SMT encoding options supported */
sealed abstract class SMTEncoding

// TODO: Move into at.forsyte.apalache.tla.lir.Feature?
object SMTEncoding {
  final case object OOPSLA19 extends SMTEncoding {
    override def toString: String = "oopsla19"
  }
  final case object Arrays extends SMTEncoding {
    override def toString: String = "arrays"
  }

  final case object FunArrays extends SMTEncoding {
    override def toString: String = "funArrays"
  }

  val ofString: String => SMTEncoding = {
    case "arrays"        => Arrays
    case "funArrays"     => FunArrays
    case "oopsla19"      => OOPSLA19
    case oddEncodingType => throw new IllegalArgumentException(s"Unexpected SMT encoding type $oddEncodingType")
  }
}

/** Defines the bmcmt model options supported */
sealed abstract class Algorithm

object Algorithm {
  final case object Incremental extends Algorithm {
    override def toString = "incremental"
  }

  final case object Offline extends Algorithm {
    override def toString = "offline"
  }

  val ofString: String => Algorithm = {
    case "incremental" => Incremental
    case "offline"     => Offline
    case invalid       => throw new IllegalArgumentException(s"Unexpected checker algorithm type $invalid")
  }
}

/** The basic interface for groups of options used to control program behavior */
sealed trait OptionGroup

/**
 * Specifies the options used to control pass executions
 *
 * Typically, each pass will need a subset of the available option groups, and the sequence of passes run by the
 * `PassExecutor` will require the union of the option groups required by its constituent passes.
 *
 * The unions can be specified via the `Has*` traits, such as [[OptionGroup.HasInput]] and constructed via the `With*`
 * classes, such as [[OptionGroup.WithInput]].
 */
object OptionGroup extends LazyLogging {

  /**
   * Interface for a group of related options that can be produced from a [[Config]]
   *
   * The intended use of this class is to identify '''configurable''' options. Configurable options are extensions of
   * `OptionGroup` that can be derived from a `Config`. Typically, these are case classes.
   *
   * @param cfg
   *   An instance of [[Config config group]].
   */
  sealed trait Configurable[C <: Config[C], +O] {
    //  TODO could manual apply methods be replaced with pureconfig merging?
    def apply(cfg: C): Try[O]
  }

  // Convert optional values into `Try`'s
  // see https://stackoverflow.com/questions/17521709/how-can-i-best-convert-an-option-into-a-try/45017589#45017589
  implicit class OptionOps[A](opt: Option[A]) {

    def toTry(field: String): Try[A] = {
      opt
        .map(Success(_))
        .getOrElse(Failure(new PassOptionException(s"Missing value for required option ${field}")))
    }
  }

  /** Options used in all modes of execution */
  case class Common(
      command: String,
      debug: Boolean,
      features: Seq[Feature],
      outDir: File,
      profiling: Boolean,
      runDir: Option[File],
      smtprof: Boolean,
      writeIntermediate: Boolean)
      extends OptionGroup

  object Common extends Configurable[Config.Common, Common] {
    // NOTE: These conversions can probably be automated via some
    // clever use of shapeless records, but not sure if it's worth the
    // complexity at this point.
    //
    // If we change the needed options so that all values are non `Option`, the
    // automated conversion would be trivially.
    //
    def apply(common: Config.Common): Try[Common] = {
      for {
        // Required fields
        command <- common.command.toTry("common.command")
        debug <- common.debug.toTry("debug")
        features <- common.features.toTry("common.features")
        outDir <- common.outDir.toTry("common.outDir")
        profiling <- common.profiling.toTry("common.profiling")
        smtprof <- common.smtprof.toTry("common.smtprof")
        writeIntermediate <- common.writeIntermediate.toTry("common.writeIntermediate")
      } yield Common(
          command = command,
          debug = debug,
          features = features,
          outDir = outDir,
          profiling = profiling,
          runDir = common.runDir, // Remains optional
          smtprof = smtprof,
          writeIntermediate = writeIntermediate,
      )
    }
  }

  /** Options used to configure program input */
  case class Input(source: SourceOption) extends OptionGroup

  object Input extends Configurable[Config.Input, Input] {
    def apply(input: Config.Input): Try[Input] = for {
      source <- input.source.toTry("input.source")
    } yield Input(source)
  }

  /** Options used to configure program output */
  case class Output(output: Option[File]) extends OptionGroup

  object Output extends Configurable[Config.Output, Output] {
    def apply(output: Config.Output): Try[Output] = Try(Output(output = output.output))
  }

  /** Options used to configure the typechecker */
  case class Typechecker(inferpoly: Boolean) extends OptionGroup

  object Typechecker extends Configurable[Config.Typechecker, Typechecker] {
    def apply(typechecker: Config.Typechecker): Try[Typechecker] = for {
      inferpoly <- typechecker.inferpoly.toTry("typechecker.inferpoly")
    } yield Typechecker(inferpoly)
  }

  /** Options used to rack specification predicates */
  case class Predicates(
      behaviorSpec: BehaviorSpec,
      cinit: Option[String],
      invariants: List[String],
      temporalProps: List[String],
      tlcConfig: Option[(TlcConfig, File)],
      view: Option[String])
      extends OptionGroup

  // The `Predicates` option group loads configurations both from the usual
  // sorces indicated by extending the `Configurable` class AND from TLC `.cfg`
  // files, if such a file is specified in the usual configs. As a result, its
  // configuration logic is much more complex than that of any other option group.
  //
  // Some of this complexity may be reduced in the future by figuring out how we
  // can wire the TLC `.cfg` file into the existing configuration system.
  object Predicates extends Configurable[Config.Checker, Predicates] {

    // Enables uniform reporting of overriden configuration values
    abstract private class EmptyShowable[T] {
      def isEmpty(t: T): Boolean
      def toString(t: T): String
      def empty: T
    }

    // Implements required operations on the types of overrideable values
    private object EmptyShowable {
      implicit object stringList extends EmptyShowable[List[String]] {
        def isEmpty(t: List[String]) = t.isEmpty
        def toString(t: List[String]) = t.mkString(", ")
        def empty = List.empty
      }

      implicit object string extends EmptyShowable[String] {
        def isEmpty(t: String) = t.isEmpty
        def toString(t: String) = t
        def empty = ""
      }
    }

    def apply(checker: Config.Checker): Try[Predicates] = {
      // To derive the `Predicates` options group, we may need to load a TLC
      // `.cfg` file such a file was specified by the input configuration.
      checker.config match {
        case None =>
          // No TLC config was given, so derive all the predicate options from
          // the input configuration.
          Try(Predicates(
                  behaviorSpec = InitNextSpec(init = checker.initOrDefault, next = checker.nextOrDefault),
                  cinit = checker.cinit,
                  invariants = checker.invOrDefault,
                  temporalProps = checker.temporalPropsOrDefault,
                  tlcConfig = None,
                  view = checker.view,
              ))

        case Some(fname) =>
          // A TLC config was given, so we need to try loading it, and determine
          // whether to use it's values or if they should be overridden by values
          // from the input configuration.
          for {
            tlcConfig <- Try(loadTLCCfg(fname))
            behaviorSpec =
              tlcConfig.behaviorSpec match {
                case InitNextSpec(cfgInit, cfgNext) =>
                  // Init and Next predicates were specified in the TLC config
                  // but we may need to override them with CLI or apalache.cfg config values
                  val init = tryToOverrideFromCli(checker.init, cfgInit, "init")
                  val next = tryToOverrideFromCli(checker.next, cfgNext, "next")
                  InitNextSpec(init = init, next = next)
                case spec => spec // Any other behavior spec from the TLC config we can use as is
              }

            temporalProps = tryToOverrideFromCli(checker.temporalProps, tlcConfig.temporalProps, "temporal")
            invariants = tryToOverrideFromCli(checker.inv, tlcConfig.invariants, "inv")
          } yield Predicates(
              behaviorSpec = behaviorSpec,
              cinit = checker.cinit,
              invariants = invariants,
              temporalProps = temporalProps,
              tlcConfig = Some((tlcConfig, fname)),
              view = checker.view,
          )
      }
    }

    private def loadTLCCfg(f: File): TlcConfig = {
      if (!f.exists()) {
        throw new PassOptionException(s"Specified TLC config file not found: ${f.getAbsolutePath()}")
      }
      val basename = f.getName()
      logger.info(s"  > $basename: Loading TLC configuration")
      try {
        TlcConfigParserApalache(new FileReader(f))
      } catch {
        case e: IOException =>
          val msg = s"  > $basename: IO error when loading the TLC config: ${e.getMessage}"
          throw new PassOptionException(msg)

        case e: TlcConfigParseError =>
          val msg = s"  > $basename:${e.pos}:  Error parsing the TLC config file: ${e.msg}"
          throw new PassOptionException(msg)
      }
    }

    // Override TLCConfig values from CLI/Config args, if the latter are given.
    // Also report the resulting value and source from which the configuration
    // ultimately loaded.
    private def tryToOverrideFromCli[T](
        cliValue: Option[T],
        tlcConfigValue: T,
        name: String,
      )(implicit es: EmptyShowable[T]): T = cliValue match {
      case Some(v) =>
        val msg =
          s"  >  $name is set in TLC config but overridden via `$name` cli option or apalache.cfg; using ${es.toString(v)}"
        logger.warn(msg)
        v
      case None if !(es.isEmpty(tlcConfigValue)) =>
        logger.info(s"  > Using $name predicate(s) ${es.toString(tlcConfigValue)} from the TLC config")
        tlcConfigValue
      case _ => es.empty
    }
  }

  /** Options used to configure trace evaluation. */
  case class Tracee(
      trace: SourceOption,
      expressions: List[String])
      extends OptionGroup

  object Tracee extends Configurable[Config.Tracee, Tracee] with LazyLogging {
    def apply(tracee: Config.Tracee): Try[Tracee] = {

      def validateExprs(lst: List[String]): Try[List[String]] =
        if (lst.nonEmpty) Success(lst)
        else Failure(new PassOptionException("Trace evaluation requires a nonempty list of expressions."))

      def validateSource(sourceOption: SourceOption): Try[SourceOption] = sourceOption.format match {
        case SourceOption.Format.Itf | SourceOption.Format.Json => Success(sourceOption)
        case _ => Failure(new PassOptionException("Trace evaluation requires an ITF or JSON trace."))
      }

      for {
        trace <- tracee.trace.toTry("trace.trace").flatMap(validateSource)
        expressions <- tracee.expressions.toTry("trace.expressions").flatMap(validateExprs)
      } yield Tracee(
          trace = trace,
          expressions = expressions,
      )
    }
  }

  /** Options used to configure model checking */
  case class Checker(
      algo: Algorithm,
      discardDisabled: Boolean,
      length: Int,
      maxError: Int,
      noDeadlocks: Boolean,
      nworkers: Int,
      smtEncoding: SMTEncoding,
      tuning: Map[String, String])
      extends OptionGroup

  object Checker extends Configurable[Config.Checker, Checker] with LazyLogging {
    def apply(checker: Config.Checker): Try[Checker] = {

      def validateMaxError(n: Int) =
        if (n > 1 && checker.view.isEmpty) {
          val msg = s"Option maxError = ${n} requires a view. None specified."
          Failure(new PassOptionException(msg))
        } else {
          Success(n)
        }

      for {
        algo <- checker.algo.toTry("checker.algo")
        discardDisabled <- checker.discardDisabled.toTry("checker.discardDisabled")
        length <- checker.length.toTry("checker.length")
        noDeadlocks <- checker.noDeadlocks.toTry("checker.noDeadlocks")
        nworkers <- checker.nworkers.toTry("checker.nworkers")
        smtEncoding <- checker.smtEncoding.toTry("checker.smtEncoding")
        tuning <- checker.tuning.toTry("checker.tuning")
        maxError <- checker.maxError.toTry("checker.maxError").flatMap(validateMaxError)
      } yield Checker(
          algo = algo,
          discardDisabled = discardDisabled,
          length = length,
          maxError = maxError,
          noDeadlocks = noDeadlocks,
          nworkers = nworkers,
          smtEncoding = smtEncoding,
          tuning = tuning,
      )
    }
  }

  /** Options used to configure the server */
  case class Server(
      port: Int)
      extends OptionGroup

  object Server extends Configurable[Config.Server, Server] {
    def apply(server: Config.Server): Try[Server] = for {
      port <- server.port.toTry("server.port")
    } yield Server(
        port = port
    )
  }

  ////////////////
  // Interfaces //
  ////////////////

  // The following traits specify combinations of needed options.

  trait HasCommon extends OptionGroup {
    val common: Common
  }

  trait HasServer extends HasCommon {
    val server: Server
  }

  trait HasInput extends HasCommon {
    val input: Input
  }

  trait HasOutput extends HasCommon {
    val output: Output
  }

  trait HasIO extends HasInput with HasOutput

  trait HasTypechecker extends HasIO {
    val typechecker: Typechecker
  }

  trait HasChecker extends HasTypechecker {
    val checker: Checker
  }

  /**
   * Interface for the set of options used when computing derived predicates
   *
   * Set of option groups should only be required by the `ConfigurationPassImpl`, and should be replaced by
   * `DerivedPredicates` in subsequent passes.
   */
  trait HasCheckerPreds extends HasChecker {
    val predicates: Predicates
  }

  trait HasTracee extends HasCheckerPreds {
    val tracee: Tracee
  }

  /**
   * The maximal set of option groups
   *
   * that should always be the greatest upper bound on all combinations of option groups
   */
  trait HasAll extends HasTracee

  //////////////////
  // Constructors //
  //////////////////

  // The following classes provide ways of constructing the option group
  // combinations specified in the interfaces above.

  /** The empty option group, providing no values */
  case class WithNone() extends OptionGroup

  case class WithInput(
      common: Common,
      input: Input)
      extends HasInput

  object WithInput extends Configurable[Config.ApalacheConfig, WithInput] {
    def apply(cfg: Config.ApalacheConfig): Try[WithInput] = for {
      common <- Common(cfg.common)
      input <- Input(cfg.input)
    } yield WithInput(common, input)
  }

  case class WithOutput(
      common: Common,
      output: Output)
      extends HasOutput

  object WithOutput extends Configurable[Config.ApalacheConfig, WithOutput] {
    def apply(cfg: Config.ApalacheConfig): Try[WithOutput] = for {
      common <- Common(cfg.common)
      output <- Output(cfg.output)
    } yield WithOutput(common, output)
  }

  case class WithServer(
      common: Common,
      server: Server)
      extends HasServer

  object WithServer extends Configurable[Config.ApalacheConfig, WithServer] {
    def apply(cfg: Config.ApalacheConfig): Try[WithServer] = for {
      common <- Common(cfg.common)
      server <- Server(cfg.server)
    } yield WithServer(common, server)
  }

  case class WithIO(
      common: Common,
      input: Input,
      output: Output)
      extends HasIO

  object WithIO extends Configurable[Config.ApalacheConfig, WithIO] {
    def apply(cfg: Config.ApalacheConfig): Try[WithIO] = for {
      input <- WithInput(cfg)
      output <- WithOutput(cfg)
    } yield WithIO(input.common, input.input, output.output)
  }

  case class WithTypechecker(
      common: Common,
      input: Input,
      output: Output,
      typechecker: Typechecker)
      extends HasTypechecker

  object WithTypechecker extends Configurable[Config.ApalacheConfig, WithTypechecker] {
    def apply(cfg: Config.ApalacheConfig): Try[WithTypechecker] = for {
      io <- WithIO(cfg)
      typechecker <- Typechecker(cfg.typechecker)
    } yield WithTypechecker(common = io.common, input = io.input, output = io.output, typechecker)
  }

  case class WithChecker(
      common: Common,
      input: Input,
      output: Output,
      typechecker: Typechecker,
      checker: Checker)
      extends HasChecker

  object WithChecker extends Configurable[Config.ApalacheConfig, WithChecker] {
    def apply(cfg: Config.ApalacheConfig): Try[WithChecker] = for {
      opts <- WithTypechecker(cfg)
      checker <- Checker(cfg.checker)
    } yield WithChecker(opts.common, opts.input, opts.output, opts.typechecker, checker)
  }

  case class WithTracee(
      common: Common,
      input: Input,
      output: Output,
      typechecker: Typechecker,
      checker: Checker,
      predicates: Predicates,
      tracee: Tracee)
      extends HasTracee

  object WithTracee extends Configurable[Config.ApalacheConfig, WithTracee] {
    def apply(cfg: Config.ApalacheConfig): Try[WithTracee] = for {
      opts <- WithCheckerPreds(cfg)
      tracee <- Tracee(cfg.tracee)
    } yield WithTracee(
        opts.common,
        opts.input,
        opts.output,
        opts.typechecker,
        opts.checker,
        opts.predicates,
        tracee,
    )
  }

  case class WithCheckerPreds(
      common: Common,
      input: Input,
      output: Output,
      typechecker: Typechecker,
      checker: Checker,
      predicates: Predicates)
      extends HasCheckerPreds

  object WithCheckerPreds extends Configurable[Config.ApalacheConfig, WithCheckerPreds] {
    def apply(cfg: Config.ApalacheConfig): Try[WithCheckerPreds] = for {
      opts <- WithChecker(cfg)
      predicates <- Predicates(cfg.checker)
    } yield WithCheckerPreds(
        opts.common,
        opts.input,
        opts.output,
        opts.typechecker,
        opts.checker,
        predicates,
    )
  }
}
