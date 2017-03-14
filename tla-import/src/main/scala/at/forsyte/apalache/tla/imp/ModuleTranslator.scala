package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{TlaConstDecl, TlaDecl, TlaModule, TlaVarDecl}
import tla2sany.semantic.{ExprOrOpArgNode, ModuleNode, OpDefNode}

/**
  * Translate a tla2tools ModuleNode to a TlaModule.
  *
  * @author konnov
  */
class ModuleTranslator {
  def translate(node: ModuleNode): TlaModule = {
    val context1 = node.getConstantDecls.toList.foldLeft(Context()) {
      (ctx, node) => ctx.push(TlaConstDecl(node.getName.toString))
    }
    val context2 = node.getVariableDecls.toList.foldLeft(context1) {
      (ctx, node) => ctx.push(TlaVarDecl(node.getName.toString))
    }
    val context = node.getOpDefs.toList.foldLeft(context2) {
      (ctx, node) => ctx.push(OpDefTranslator(ctx).translate(node))
    }
    // TODO: add the source info into a proper database
    new TlaModule(node.getName.toString, Seq(), context.declarations)
  }
}

object ModuleTranslator {
  def apply(): ModuleTranslator = {
    new ModuleTranslator()
  }
}
