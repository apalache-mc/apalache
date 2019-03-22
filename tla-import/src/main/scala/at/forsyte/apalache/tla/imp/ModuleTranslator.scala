package at.forsyte.apalache.tla.imp


import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{EnvironmentHandler, TlaConstDecl, TlaModule, TlaVarDecl}
import tla2sany.semantic.ModuleNode

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * Translate a tla2tools ModuleNode to a TlaModule.
  *
  * @author konnov
  */
class ModuleTranslator(environmentHandler: EnvironmentHandler, sourceStore: SourceStore) {
  // TODO: get rid of environmentHandler, we do not need it anymore

  def translate(node: ModuleNode): TlaModule = {
    var context = node.getConstantDecls.toList.foldLeft(Context()) {
      (ctx, node) => ctx.push(TlaConstDecl(node.getName.toString))
    }
    context = node.getVariableDecls.toList.foldLeft(context) {
      (ctx, node) => ctx.push(TlaVarDecl(node.getName.toString))
    }
    val excludedDefs = findExcludedDefs(node)
    val userDefs = node.getOpDefs.toList filter (df => !excludedDefs.contains(df.getName.toString))
    context = userDefs.foldLeft(context) {
      (ctx, node) => ctx.push(OpDefTranslator(environmentHandler, sourceStore, ctx).translate(node))
    }
    // translate assumptions after the operator definitions, as the assumptions may use the operators
    context = node.getAssumptions.toList.foldLeft(context) {
      (ctx, node) => ctx.push(AssumeTranslator(environmentHandler, sourceStore, ctx).translate(node))
    }
    val imported = node.getExtendedModuleSet.toArray(Array[ModuleNode]()).map {
      mn => mn.getName.toString.intern()
    }
    // TODO: add the source info into a proper database
    new TlaModule(node.getName.toString, imported, context.declarations)
  }

  private def findExcludedDefs(node: ModuleNode): Set[String] = {
    var excludedDefs = HashSet[String]()
    for (module <- node.getExtendedModuleSet.asScala) {
      val mod = module.asInstanceOf[ModuleNode]
      if (ModuleTranslator.overloadedModules.contains(mod.getName.toString)) {
        excludedDefs ++= (mod.getOpDefs map (_.getName.toString.intern()))
      }
    }

    excludedDefs
  }
}

object ModuleTranslator {
  /**
    * The operators in the following modules are overloaded by the importer, so we exclude their
    * operator definitions from the user modules. (Moreover, the standard modules sometimes contain garbage
    * or complex definitions that should not be analyzed by the our tool.)
    */
  val overloadedModules: Set[String] = Set("Naturals", "Integers", "Sequences", "TLC", "FiniteSets", "Reals")

  def apply(environmentHandler: EnvironmentHandler, sourceStore: SourceStore): ModuleTranslator = {
    new ModuleTranslator(environmentHandler, sourceStore)
  }
}
