package at.forsyte.apalache.infra.passes.options

// TODO: Use either File or Path consistently (preference for File)
import java.io.File
import at.forsyte.apalache.tla.lir.Feature
import com.google.inject.Provider
import com.google.inject.ProvisionException
import scala.util.Try
import scala.util.Success
import scala.util.Failure

/**
 * Collects the options supported for configuring Apalache's various modes of execution
 *
 * @author
 *   Shon Feder
 */

object Config {

  /** The application's configurable values, along with their base defaults */
  // TODO Rename to "Common"
  case class Common(
      /** The subcommand or process being executed */
      routine: Option[String] = None,
      file: Option[File] = None,
      outDir: Option[File] = None,
      runDir: Option[File] = None,
      debug: Option[Boolean] = None,
      smtprof: Boolean = false,
      configFile: Option[File] = None,
      writeIntermediate: Option[Boolean] = None,
      profiling: Option[Boolean] = None,
      /** Enables features protected by feature-flags */
      features: Option[Seq[Feature]] = None)
  object Common {
    val default =
      Common(routine = Some("UNCONFIGURED-ROUTINE"), file = None,
          outDir = Some(new File(System.getProperty("user.dir"), "_apalache-out")), runDir = None, debug = Some(false),
          smtprof = false, configFile = None, writeIntermediate = None, profiling = None, features = Some(Seq()))
  }

  case class Output(
      /** A file into which output can be written */
      output: Option[File] = None)

  object Output {
    val default = Output()
  }

  // TODO: Switch defaults and empty values
  // TODO: Add values to feed to `Checker` options group
  case class Checker(
      tuning: Map[String, String] = Map(), // TODO make optional
      algo: Option[String] = None, // TODO: convert to case class
      cinit: Option[String] = None, // "",
      config: Option[String] = None, // ""
      discardDisabled: Option[Boolean] = None, // true,
      init: Option[String] = None, // ""
      inv: Option[String] = None, // TODO Should be list?
      length: Option[Int] = None,
      maxError: Option[Int] = None,
      next: Option[String] = None,
      noDeadlocks: Option[Boolean] = None,
      nworkers: Option[Int] = None,
      smtEncoding: Option[SMTEncoding] = None,
      temporal: Option[String] = None, // TODO SHould be list?
      view: Option[String] = None)

  object Checker {
    val default = Checker(tuning = Map(), algo = Some("incremental"), cinit = None, config = None,
        discardDisabled = Some(true), init = Some("Init"), inv = None, length = Some(10), maxError = Some(1),
        next = Some("Next"), noDeadlocks = Some(false), nworkers = Some(1), smtEncoding = Some(SMTEncoding.OOPSLA19),
        temporal = None, view = None)
  }
  // TODO implement to achieve parity with options
  // case class Input()

  // TODO
  case class Typechecker(
      inferpoly: Option[Boolean] = None)

  object Typechecker {
    val default = Typechecker(
        inferpoly = Some(false)
    )
  }

  case class ApalacheConfig(
      common: Common = Common(),
      output: Output = Output(),
      checker: Checker = Checker(),
      typechecker: Typechecker = Typechecker())

  object ApalacheConfig {
    val default = ApalacheConfig(
        common = Common.default,
        output = Output.default,
        checker = Checker.default,
        typechecker = Typechecker.default,
    )

  }

  // Fix formatting to put each value on own line
}

// TODO rm
import Config._

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
      configFile: Option[File],
      smtprof: Boolean,
      profiling: Boolean,
      outDir: File,
      runDir: Option[File], // TODO Should be optional?
      writeIntermediate: Boolean,
      debug: Boolean,
      features: Seq[Feature])

  object Common extends Configurable[Common] {
    def apply(cfg: ApalacheConfig): Try[Common] =
      // TODO: Move defaults into case class?
      Success(Common(
              configFile = cfg.common.configFile,
              smtprof = cfg.common.smtprof,
              profiling = cfg.common.profiling.getOrElse(false),
              outDir = cfg.common.outDir.getOrElse(new File(System.getProperty("user.dir"), "_apalache-out")),
              runDir = cfg.common.runDir,
              writeIntermediate = getConfig(cfg.common.writeIntermediate, "write-intermediate"),
              debug = cfg.common.debug.getOrElse(false),
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

// case class Parse(cfg: ApalacheConfig) extends Configurable(cfg) with IO {
//   val input: Common = Common(cfg)
//   val debug:
// }

/**
 * Provides a configured option instance via a Google Guice Provider
 *
 * The [[OptionsProvider]] enables late binding of a configured option instance supplied to all classes via the Guice
 * dependency injection
 */
class OptionsProvider[T] extends Provider[T] {
  protected var _options: Option[T] = None

  def configure(opt: ApalacheConfig => Try[T], cfg: ApalacheConfig): Try[Unit] =
    opt(cfg).map(os => _options = Some(os))

  def get(): T = _options.getOrElse(throw new ProvisionException("pass options were not configured"))
}

// Yeah!
class test {
  import OptionGroup._
  val op: OptionsProvider[Output] = new OptionsProvider[Output]()
  val t = op.configure(Output(_), ApalacheConfig())
  val ops = op.get().output
}
