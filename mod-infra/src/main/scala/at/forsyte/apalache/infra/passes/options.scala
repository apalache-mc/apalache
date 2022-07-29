package at.forsyte.apalache.infra.passes

/** Collects the passoptions supported for configuring Apalache's various passes */
object options {

  /** Defines the data sources supported in the [[PassOptions]] */
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

  /**
   * Defines the SMT encoding options supported
   *
   * @author
   *   Shon Feder
   */
  sealed abstract class SMTEncoding

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
}
