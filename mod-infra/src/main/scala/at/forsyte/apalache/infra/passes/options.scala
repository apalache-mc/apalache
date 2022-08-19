package at.forsyte.apalache.infra.passes.options

import java.io.File
import at.forsyte.apalache.tla.lir.Feature
import scala.util.{Failure, Success, Try}
import at.forsyte.apalache.infra.PassOptionException

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
      inputfile: Option[File] = None, // TODO Move "inputfile" into an "Input" configuration group
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
   *   the name of an invariant operator
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
   * @param temporal
   *   the name of a temporal property, e.g. Property
   * @param view
   *   the state view to use for generating counter examples when `maxError` is set
   */
  case class Checker(
      tuning: Option[Map[String, String]] = Some(Map()),
      algo: Option[String] = Some("incremental"), // TODO: convert to case class
      config: Option[String] = None,
      discardDisabled: Option[Boolean] = Some(true),
      cinit: Option[String] = None,
      init: Option[String] = None, // TODO Set proper default here once ConfigurationPassImpl is fixed
      inv: Option[String] = None, // TODO Should be list?
      next: Option[String] = None, // TODO Set proper default here once ConfigurationPassImpl is fixed
      length: Option[Int] = Some(10),
      maxError: Option[Int] = Some(1),
      noDeadlocks: Option[Boolean] = Some(false),
      nworkers: Option[Int] = Some(1),
      smtEncoding: Option[SMTEncoding] = Some(SMTEncoding.OOPSLA19),
      temporal: Option[String] = None, // TODO SHould be list?
      view: Option[String] = None)
      extends Config[Checker] {

    def empty: Checker = Generic[Checker].from(Generic[Checker].to(this).map(emptyPoly))
  }

  /**
   * Configuration of type checking
   *
   * @param inferpoly
   *   allow the type checker to infer polymorphic types
   */
  case class Typechecker(
      inferpoly: Option[Boolean] = Some(false))
      extends Config[Typechecker] {

    def empty: Typechecker = Generic[Typechecker].from(Generic[Typechecker].to(this).map(emptyPoly))
  }

  /**
   * The complete configuration
   *
   * Gathers all configuration groups
   */
  case class ApalacheConfig(
      common: Common = Common(),
      output: Output = Output(),
      checker: Checker = Checker(),
      typechecker: Typechecker = Typechecker())
      extends Config[ApalacheConfig] {

    def empty: ApalacheConfig = Generic[ApalacheConfig].from(Generic[ApalacheConfig].to(this).map(emptyPoly))
  }
}

/** Defines the data sources supported */
sealed abstract class SourceOption

object SourceOption {

  /** Data to be loaded from a file */
  final case class FileSource(file: java.io.File) extends SourceOption

  /**
   * Data supplied as a string
   *
   * @param content
   *   the principle data source
   * @param aux
   *   auxiliary data sources
   */
  final case class StringSource(content: String, aux: Seq[String] = Seq()) extends SourceOption
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
object OptionGroup {

  /**
   * Interface for a group of related options that can be produced from a [[Config]]
   *
   * The intended use of this class is to identify '''configurable''' options. Configurable options are extensions of
   * `OptionGroup` that can be derived from a `Config`. Typically, these are case classes.
   *
   * @param cfg
   *   An instance of [[Config config group]].
   */
  sealed trait Configurable[C <: Config[C], O] {
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
        smtprof <- common.debug.toTry("common.smtprog")
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

  object Input extends Configurable[Config.Common, Input] {
    def apply(common: Config.Common): Try[Input] = for {
      file <- common.inputfile.toTry("input.source")
    } yield Input(SourceOption.FileSource(file.getAbsoluteFile))
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

  /** Options used to configure model checking */
  case class Checker(
      algo: String,
      cinit: Option[String],
      config: Option[String], // TODO: rm once ConfigurationPassImpl is moved into configuration stage
      discardDisabled: Boolean,
      init: Option[String], // TODO Make required after ConfigurationPassImpl is refactored
      inv: Option[String],
      length: Int,
      maxError: Int,
      next: Option[String], // TODO Make required after ConfigurationPassImpl is refactored
      noDeadlocks: Boolean,
      nworkers: Int,
      smtEncoding: SMTEncoding,
      temporal: Option[String],
      tuning: Map[String, String],
      view: Option[String])
      extends OptionGroup

  object Checker extends Configurable[Config.Checker, Checker] {
    def apply(checker: Config.Checker): Try[Checker] = for {
      // Required options
      algo <- checker.algo.toTry("checker.algo")
      discardDisabled <- checker.discardDisabled.toTry("checker.discardDisabled")
      // init <- checker.init.toTry("checker.init")
      length <- checker.length.toTry("checker.length")
      maxError <- checker.maxError.toTry("checker.maxError")
      // next <- checker.next.toTry("checker.next")
      noDeadlocks <- checker.noDeadlocks.toTry("checker.noDeadlocks")
      nworkers <- checker.nworkers.toTry("checker.nworkers")
      smtEncoding <- checker.smtEncoding.toTry("checker.smtEncoding")
      tuning <- checker.tuning.toTry("checker.tuning")
    } yield Checker(
        algo = algo,
        cinit = checker.cinit, // optional
        config = checker.config, // optional
        discardDisabled = discardDisabled,
        init = checker.init, // TODO: should be required
        inv = checker.inv, // optional
        length = length,
        maxError = maxError,
        next = checker.next, // TODO: should be required
        noDeadlocks = noDeadlocks,
        nworkers = nworkers,
        smtEncoding = smtEncoding,
        temporal = checker.temporal, // optional
        tuning = tuning,
        view = checker.view, // optional
    )
  }

  ////////////////
  // Interfaces //
  ////////////////

  // The following traits specify combinations of needed options.

  trait HasCommon extends OptionGroup {
    val common: Common
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

  // This is the maximal interface, that should always be the greatest upper
  // bound on all combinations of option groups
  trait HasAll extends HasChecker

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
      input <- Input(cfg.common)
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
}
