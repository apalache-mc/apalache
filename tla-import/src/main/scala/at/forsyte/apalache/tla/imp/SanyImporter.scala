package at.forsyte.apalache.tla.imp

import java.io._

import at.forsyte.apalache.tla.lir.TlaModuleDecl
import org.apache.commons.io.output.WriterOutputStream
import tla2sany.drivers.SANY
import tla2sany.modanalyzer.SpecObj
import util.SimpleFilenameToStream

import scala.io.Source

/**
  * This is the entry point for parsing TLA+ code with SANY and constructing an IR.
  *
  * @author konnov
  */
class SanyImporter {
  /**
    * Load a TLA+ specification from a text source. This method creates a temporary file and saves the source's contents
    * into it, in order to call SANY.
    *
    * @param source the text source
    * @return the pair (the root module name, a map of modules)
    */
  def load(source: Source): (String, Map[String, TlaModuleDecl]) = {
    val temp = File.createTempFile("temp", ".tla")
    try {
      // write the contents to a temporary file
      val pw = new PrintWriter(temp)
      try { source.getLines().foreach(line => pw.write(line)) } finally { pw.close() }
      // create a string buffer to write the error messages from SANY
      val errBuf = new StringWriter() // use.toString() to retrieve the error messages
      val specObj = new SpecObj(temp.getAbsolutePath, new SimpleFilenameToStream())
      // call SANY and pray it works :-)
      // FIXME: do some error analysis here
      SANY.frontEndMain(specObj, temp.getAbsolutePath, new PrintStream(new WriterOutputStream(errBuf, "UTF8")))
      Tuple2(specObj.getName, Map())
    } finally {
      temp.delete()
    }
  }
}
