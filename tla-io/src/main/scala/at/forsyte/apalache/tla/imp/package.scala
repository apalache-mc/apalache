package at.forsyte.apalache.tla

import at.forsyte.apalache.io.annotations.store._

import java.io.File
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._

package object imp {

  // TODO: move it closer to the code that is actually using this helper method?
  def declarationsFromFile(p_path: String): Seq[TlaDecl] = {
    val (rootName, modules) =
      new SanyImporter(new SourceStore, createAnnotationStore())
        .loadFromFile(new File(p_path))
    modules(rootName).declarations
  }

  // TODO: should not be this method moved to *.lir.process?
  def findBodyOf(p_opName: String, decls: TlaDecl*): TlaEx = {
    decls
      .find {
        _.name == p_opName
      }
      .withFilter(_.isInstanceOf[TlaOperDecl])
      .map(_.asInstanceOf[TlaOperDecl].body)
      .getOrElse(NullEx)
  }

}
