package at.forsyte.apalache.tla.parser

import scala.xml.XML

/**
 * A command-line to check how good our parser is.
  *
  * @deprecated
 *
 * @author Igor Konnov
 */
object XmlImporterConsole {
  def use(): Unit = {
    println("Arguments: filename.xml")
    System.exit(1)
  }

  def main(args: Array[String]): Unit = {
    Console.printf("*** APALACHE ***\n\n")
    Console.printf("XmlImporterConsole\n")

    if (args.length < 1)
      use()

    val xml = XML.loadFile(args(0))
    val spec = new XmlImporter().parse(xml)
  }
}
