package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{TlaConstDecl, TlaModule, TlaVarDecl}
import tla2sany.semantic.ModuleNode

/**
  * Translate a tla2tools ModuleNode to a TlaModule.
  *
  * @author konnov
  */
class ModuleTranslator {
  def translate(node: ModuleNode): TlaModule = {
    val varDecls = node.getVariableDecls.toList.map
      { n => TlaVarDecl(n.getName.toString) }
    val constDecls = node.getConstantDecls.toList.map
      { n => TlaConstDecl(n.getName.toString)}
    val opDefs = node.getOpDefs.toList.map
      { new OpDefTranslator().translate(_) }
    // TODO: add the source info into a proper database

    new TlaModule(node.getName.toString, Seq(), constDecls ++ varDecls ++ opDefs)
  }
}
