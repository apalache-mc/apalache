package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{EnvironmentHandler, TlaConstDecl, TlaModule, TlaVarDecl}
import tla2sany.semantic.ModuleNode

/**
  * Translate a tla2tools ModuleNode to a TlaModule.
  *
  * @author konnov
  */
class ModuleTranslator(environmentHandler: EnvironmentHandler, sourceStore: SourceStore) {
  def translate(node: ModuleNode): TlaModule = {
    val context1 = node.getConstantDecls.toList.foldLeft(Context()) {
      (ctx, node) => ctx.push(TlaConstDecl(node.getName.toString))
    }
    val context2 = node.getVariableDecls.toList.foldLeft(context1) {
      (ctx, node) => ctx.push(TlaVarDecl(node.getName.toString))
    }
    val context3 = node.getAssumptions.toList.foldLeft(context2) {
      (ctx, node) => ctx.push(AssumeTranslator(environmentHandler, sourceStore, ctx).translate(node))
    }
    val context = node.getOpDefs.toList.foldLeft(context3) {
      (ctx, node) => ctx.push(OpDefTranslator(environmentHandler, sourceStore, ctx).translate(node))
    }
    val imported = node.getExtendedModuleSet.toArray(Array[ModuleNode]()).map {
      mn => mn.getName.toString.intern()
    }
    // TODO: add the source info into a proper database
    new TlaModule(node.getName.toString, imported, context.declarations)
  }
}

object ModuleTranslator {
  def apply(environmentHandler: EnvironmentHandler, sourceStore: SourceStore): ModuleTranslator = {
    new ModuleTranslator(environmentHandler, sourceStore)
  }
}
