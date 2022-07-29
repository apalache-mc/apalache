package at.forsyte.apalache.infra.passes.options

import at.forsyte.apalache.tla.lir.Feature
import java.nio.file.Path

/**
 * Collects the passoptions supported for configuring Apalache's various passes
 *
 * @author
 *   Shon Feder
 */

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

  final case object ArraysFun extends SMTEncoding {
    override def toString: String = "arraysFun"
  }

  val ofString: String => SMTEncoding = {
    case "arrays"        => Arrays
    case "arraysFun"     => ArraysFun
    case "oopsla19"      => OOPSLA19
    case oddEncodingType => throw new IllegalArgumentException(s"Unexpected SMT encoding type $oddEncodingType")
  }
}

trait General {

  /** Tuning options control a wide variety of model checker behavior */
  // TODO: Make tuning params defined statically
  // TODO: Move these into the `Checker` options?
  val tuning: Map[String, String]
  val debug: Boolean

  /** Enables features protected by feature-flags */
  val features: Seq[Feature]
}

/** Options used to configure interaction with the SMT solver */
// TODO: Should this be removed/merged
trait Smt {
  val prof: Boolean
}

// TODO: Move into "IO"
trait Parser {
  val source: SourceOption
}

/** Options used to configure program input and output */
trait IO {
  val output: Option[String] = None
  val outdir: Path
}

trait Checker {
  val algo: String = "incremental" // TODO: convert to case class
  val cinit: String = "" // TODO: conver to optional
  val config: String = "" // TODO: convert to optional
  val discardDisabled: Boolean = true
  val init: String = "" // TODO: convert to optional
  val inv: List[String] = List()
  val length: Int = 10
  val maxError: Int = 1
  val next: String = "" // TODO: convert to optional
  val noDeadlocks: Boolean = false
  val nworkers: Int = 1
  val smtEncoding: SMTEncoding = SMTEncoding.OOPSLA19
  val temporal: List[String] = List()
  val view: String = "" // TODO: convert to optional
}

trait Typechecker {
  val inferPoly: Boolean = true
}
