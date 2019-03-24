package at.forsyte.apalache.tla.imp


import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import tla2sany.semantic.{ModuleNode, OpDefNode, SubstInNode}

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

    // Translate the operator definitions. Importantly, SANY gives us the operator definitions so that
    // if a definition A uses a definition B, then B comes before A.
    // However, this rule does not apply to the operator definitions that are declared in module instances,
    // as their bodies are rewritten by the substitution rules.
    val userDefs = node.getOpDefs.toList filter (df => !excludedDefs.contains(df.getName.toString))
    def eachOpDefFirstPass(ctx: Context, opDef: OpDefNode): Context = {
      val decl = NullOpDefTranslator(environmentHandler, sourceStore, ctx).translate(opDef)
      ctx.push(decl)
    }

    context = userDefs.foldLeft(context)(eachOpDefFirstPass)

    // second pass: produce the actual operator bodies and do substitution
    def eachOpDefSecondPass(opDef: OpDefNode): Unit = {
      val decl = context.lookup(opDef.getName.toString).get.asInstanceOf[TlaOperDecl]
      val lookupPrefix = opDef.getName.toString.split("!").dropRight(1) // find the instance names
      // the expression translator should lookup using the lookupPrefix
      val adjustedContext = context.setLookupPrefix(lookupPrefix.toList)
      val exprTranslator = ExprOrOpArgNodeTranslator(environmentHandler, sourceStore, adjustedContext, OutsideRecursion())
      opDef.getBody match {
        case substInNode: SubstInNode =>
          // override the body and do the substitution
          val body = exprTranslator.translate(substInNode.getBody)
          decl.body = SubstTranslator(environmentHandler, sourceStore, adjustedContext).translate(substInNode, body)


        case _ =>
          decl.body = exprTranslator.translate(opDef.getBody)
      }
    }

    userDefs foreach eachOpDefSecondPass

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
      // these are the definitions that come from EXTENDS Naturals, Sequences, etc.
      val mod = module.asInstanceOf[ModuleNode]
      if (ModuleTranslator.overloadedModules.contains(mod.getName.toString)) {
        excludedDefs ++= (mod.getOpDefs map (_.getName.toString.intern()))
      }
    }
    for (inst <- node.getInstances) {
      // these are the definitions that come from LOCAL INSTANCE Naturals, Sequences, etc.
      if (ModuleTranslator.overloadedModules.contains(inst.getModule.getName.toString)) {
        excludedDefs ++= (inst.getModule.getOpDefs map (_.getName.toString.intern()))
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
