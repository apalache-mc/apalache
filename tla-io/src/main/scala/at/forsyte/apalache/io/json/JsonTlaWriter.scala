package at.forsyte.apalache.io.json

import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.io.TlaType1PrinterPredefs.printer
import at.forsyte.apalache.tla.lir.io.TlaWriter
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaModule}

import java.io.PrintWriter

/**
 * An adapter between from TlaToJson and TlaWriter.
 */
class JsonTlaWriter(sourceStore: SourceStore, changeListener: ChangeListener, writer: PrintWriter) extends TlaWriter {
  private val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

  /**
   * Write a module, including all declarations
   *
   * @param module              a module
   * @param extendedModuleNames the names of the modules to be extended
   */
  override def write(module: TlaModule, extendedModuleNames: List[String]): Unit = {
    // we ignore extendedModuleNames as they are irrelevant in the JSON representation
    writer.print(new TlaToUJson(Some(sourceLocator)).makeRoot(Seq(module)).toString)
  }

  /**
   * Write a declaration, including all expressions
   *
   * @param decl a declaration
   */
  override def write(decl: TlaDecl): Unit = {
    writer.print(new TlaToUJson(Some(sourceLocator)).apply(decl).toString)
  }

  /**
   * Write a TLA+ expression.
   *
   * @param expr an expression
   */
  override def write(expr: TlaEx): Unit = {
    writer.print(new TlaToUJson(Some(sourceLocator)).apply(expr).toString)
  }
}
