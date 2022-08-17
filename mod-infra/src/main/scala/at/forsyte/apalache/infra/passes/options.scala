package at.forsyte.apalache.infra.passes.options

import java.io.File
import at.forsyte.apalache.tla.lir.Feature

/**
 * The components of this package specify the configurations and options used to configure Apalache
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
      command: Option[String] = None,
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
