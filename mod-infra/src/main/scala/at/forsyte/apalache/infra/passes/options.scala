package at.forsyte.apalache.infra.passes.options

import java.io.File
import at.forsyte.apalache.tla.lir.Feature
import com.google.inject.{Provider, ProvisionException}
import scala.util.{Failure, Success, Try}

/**
 * The components of this package specify the configurations and options used to configure Apalache
 *
 * @author
 *   Shon Feder
 */

/**
 * The basic interface of classes that specify application configurations
 */
sealed trait Config[T] {

  /**
   * Produces a copy of the config group `T` with all it's attributes (attributes nested config groups) set to `None`
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
   * @param routine
   *   The subcommand or process being executed
   * @param file
   *   The file from which input data can be read
   * @param outDir
   *   A directory into which the historical `runDir`s will be written containing diagnostic output data
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
   *   Enable experimental features
   */
  case class Common(
      routine: Option[String] = Some("UNCONFIGURED-ROUTINE"),
      file: Option[File] = None, // TODO Move "file" into an "Input" configuration group
      outDir: Option[File] = Some(new File(System.getProperty("user.dir"), "_apalache-out")),
      runDir: Option[File] = None,
      debug: Option[Boolean] = Some(false),
      smtprof: Option[Boolean] = Some(false),
      configFile: Option[File] = None,
      writeIntermediate: Option[Boolean] = None,
      profiling: Option[Boolean] = None,
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
   *   the name of an operator that initializes CONSTANTS,
   * @param discardDisabled
   *   pre-check whether a transition is disabled, and discard it, to make SMT queries smaller
   * @param init
   *   the name of an operator that initializes VARIABLES
   * @param inv
   *   the name of a transition operator
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
      // TODO Set default here once ConfigurationPassImpl is fixed
      init: Option[String] = None,
      // TODO Should be list?
      inv: Option[String] = None,
      // TODO Set default here once ConfigurationPassImpl is fixed
      next: Option[String] = None,
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
   *   allow the type checker to infer polymorphic types *
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

/**
 * A group of related options
 */
sealed trait OptionGroup

object OptionGroup {

  import Config._

  /**
   * Interface for classes that can be produced from a [[Config.ApalacheConfig]]
   *
   * The intended use of this class is to identify configurable options, which is to say case class representing program
   * configuration that can be derived from configuration input.
   *
   * @param cfg
   *   An instnace of the apalche configuration class.
   */
  sealed trait Configurable[T] {
    //  TODO could manual apply methods be replaced with pureconfig merging?
    def apply(cfg: ApalacheConfig): Try[T]
  }

  private def getConfig[T](ov: Option[T], name: String): T =
    ov.getOrElse(throw new Exception(s"TODO: Proper err ${name}"))

  /** Options used in all modes of execution */
  case class Common(
      routine: String,
      file: Option[File],
      outDir: File,
      runDir: Option[File],
      debug: Boolean,
      smtprof: Boolean,
      configFile: Option[File],
      writeIntermediate: Boolean,
      profiling: Boolean,
      features: Seq[Feature])

  object Common extends Configurable[Common] {
    def apply(cfg: ApalacheConfig): Try[Common] =
      // TODO: Move defaults into case class?
      Success(Common(
              routine = getConfig(cfg.common.routine, "routine"),
              file = cfg.common.file,
              outDir = cfg.common.outDir.getOrElse(new File(System.getProperty("user.dir"), "_apalache-out")),
              runDir = cfg.common.runDir,
              debug = cfg.common.debug.getOrElse(false),
              smtprof = cfg.common.smtprof.getOrElse(false),
              configFile = cfg.common.configFile,
              writeIntermediate = getConfig(cfg.common.writeIntermediate, "write-intermediate"),
              profiling = cfg.common.profiling.getOrElse(false),
              features = cfg.common.features.getOrElse(Seq()),
          ))
  }

  /** Options used to configure program input */
  case class Input(source: SourceOption)

  object Input extends Configurable[Input] {
    def apply(cfg: ApalacheConfig) =
      cfg.common.file match {
        case Some(file) => Success(Input(SourceOption.FileSource(file)))
        case None       => Failure(new Exception("TODO: make configuration error exception"))
      }
  }

  /** Options used to configure program output */
  case class Output(output: Option[File] = None)

  object Output extends Configurable[Output] {
    def apply(cfg: ApalacheConfig) = Success(Output(cfg.output.output))
  }

  /** Options used to configure the typechecker */
  case class Typechecker(inferPoly: Boolean = true)

  /** Options used to configure model checking */
  // TODO make configurable
  case class Checker(
      /** Tuning options control a wide variety of model checker behavior */
      // TODO: Make tuning params defined statically
      tuning: Map[String, String],
      algo: String = "incremental", // TODO: convert to case class
      cinit: String = "", // TODO: conver to optional
      config: String = "", // TODO: convert to optional
      discardDisabled: Boolean = true,
      init: String = "", // TODO: convert to optional
      inv: List[String] = List(),
      length: Int = 10,
      maxError: Int = 1,
      next: String = "", // TODO: convert to optional
      noDeadlocks: Boolean = false,
      nworkers: Int = 1,
      smtEncoding: SMTEncoding = SMTEncoding.OOPSLA19,
      temporal: List[String] = List(),
      view: String = "", // TODO: convert to optional
    )

  case class WithOutput(
      common: Common,
      output: Output)

  object WithOutput extends Configurable[WithOutput] {
    def apply(cfg: ApalacheConfig) = for {
      common <- Common(cfg)
      output <- Output(cfg)
    } yield WithOutput(common, output)
  }
}

/**
 * Provides a configured option instance via a Google Guice Provider
 *
 * The [[OptionsProvider]] enables late binding of a configured option instance supplied to all classes via the Guice
 * dependency injection
 */
class OptionsProvider[T] extends Provider[T] {
  protected var _options: Option[T] = None

  def configure(opt: Config.ApalacheConfig => Try[T], cfg: Config.ApalacheConfig): Try[Unit] =
    opt(cfg).map(os => _options = Some(os))

  def get(): T = _options.getOrElse(throw new ProvisionException("pass options were not configured"))
}

// Example of using the configuration provider
// TODO  rm once provider is integrated into Guice pipeline
class test {
  import OptionGroup._
  // Creation of the provider will happen during the DI priming
  val provider: OptionsProvider[WithOutput] = new OptionsProvider[WithOutput]()
  // This is how we will late-bind a particular option-set to the provider
  // (when setting up the Executor)
  val configure = provider.configure(WithOutput(_), Config.ApalacheConfig()).get
  // This is an example of accessing a value from the options provider
  val ops: Boolean = provider.get().common.profiling
}
