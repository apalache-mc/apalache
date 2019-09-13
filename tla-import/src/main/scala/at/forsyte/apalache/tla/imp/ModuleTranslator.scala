package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import tla2sany.semantic.{InstanceNode, ModuleNode, OpDefNode}

import scala.collection.JavaConverters._

/**
  * Translate a tla2tools ModuleNode to a TlaModule.
  *
  * @author konnov
  */
class ModuleTranslator(sourceStore: SourceStore) {
  def translate(node: ModuleNode): TlaModule = {
    var context = node.getConstantDecls.toList.foldLeft(Context()) {
      (ctx, node) => ctx.push(DeclUnit(TlaConstDecl(node.getName.toString)))
    }
    context = node.getVariableDecls.toList.foldLeft(context) {
      (ctx, node) => ctx.push(DeclUnit(TlaVarDecl(node.getName.toString)))
    }

    // Find the definitions that stem from the standard modules and declare them as aliases of the built-in operators
    context = addAliasesOfBuiltins(context, "", node)

    // Translate the operator definitions. Importantly, SANY gives us the operator definitions so that
    // if a definition A uses a definition B, then B comes before A.
    // However, this rule does not apply to the operator definitions that are declared in module instances,
    // as their bodies are rewritten by the substitution rules.
    val opDefs = node.getOpDefs.toList

    def eachOpDefFirstPass(ctx: Context, opDef: OpDefNode): Context = {
      context.lookup(opDef.getName.toString) match {
        case d: DeclUnit => throw new SanyImporterException("Duplicate definition: " + d.name)

        case NoneUnit() =>
          // translate only the user-defined operators, skip the aliases
          val decl = NullOpDefTranslator(sourceStore, ctx).translate(opDef)
          ctx.push(DeclUnit(decl))

        case _ => ctx // skip the aliases
      }
    }

    context = opDefs.foldLeft(context)(eachOpDefFirstPass)

    // second pass: produce the actual operator bodies and do substitution
    def eachOpDefSecondPass(opDef: OpDefNode): Unit = {
      context.lookup(opDef.getName.toString) match {
        case DeclUnit(decl: TlaOperDecl) =>
          val lookupPrefix = opDef.getName.toString.split("!").dropRight(1) // find the instance names
        // the expression translator should lookup using the lookupPrefix
        val adjustedContext = context.setLookupPrefix(lookupPrefix.toList)
          val defTranslator = OpDefTranslator(sourceStore, adjustedContext)
          val updatedDecl = defTranslator.translate(opDef)
          decl.isRecursive = updatedDecl.isRecursive
          decl.body = updatedDecl.body

        case _ => () // XXX: do something?
      }
    }

    opDefs foreach eachOpDefSecondPass

    // translate assumptions after the operator definitions, as the assumptions may use the operators
    context = node.getAssumptions.toList.foldLeft(context) {
      (ctx, node) => ctx.push(DeclUnit(AssumeTranslator(sourceStore, ctx).translate(node)))
    }
    val imported = node.getExtendedModuleSet.toArray(Array[ModuleNode]()).map {
      mn => mn.getName.toString.intern()
    }

    // filter out the aliases, keep only the user definitions and declarations
    val actualDefs = context.declarations.collect({ case DeclUnit(d) => d })
    new TlaModule(node.getName.toString, imported, actualDefs)
  }

  private def addAliasesOfBuiltins(ctx: Context, instancePrefix: String, node: ModuleNode): Context = {
    // declare a library definition as an operator alias
    def subDef(ctx: Context, modName: String, alias: String, opDefNode: OpDefNode): Context = {
      val opName = opDefNode.getName.toString.intern()
      var newCtx = ctx
      StandardLibrary.libraryOperators.get((modName, opName)).collect {
        case oper => newCtx = newCtx.push(OperAliasUnit(alias, oper))
      }
      StandardLibrary.globalOperators.get(opName).collect {
        case oper => newCtx = newCtx.push(OperAliasUnit(alias, oper))
      }
      StandardLibrary.libraryValues.get((modName, opName)).collect {
        case value => newCtx = newCtx.push(ValueAliasUnit(alias, value))
      }
      newCtx
    }

    def alias(d: OpDefNode): String = {
      val name = d.getName.toString.intern()
      // add the prefix of this instance, e.g., A!B!
      if (instancePrefix == "") name else instancePrefix + "!" + name
    }

    // add aliases for the definitions inside the module
    val modName = node.getName.toString
    var newCtx =
      if (StandardLibrary.standardModules.contains(modName)) {
        node.getOpDefs.foldLeft(ctx) { (c, d) => subDef(c, modName, alias(d), d) }
      } else {
        ctx
      }

    // add aliases for the definitions in the modules that this one EXTENDS
    val extendedModules = node.getExtendedModuleSet.asScala.toList map (_.asInstanceOf[ModuleNode])
    newCtx = extendedModules.foldLeft(newCtx) { (c, m) => addAliasesOfBuiltins(c, instancePrefix, m) }

    // add aliases for the definitions that come from the INSTANCE declarations
    def eachInstance(ctx: Context, inst: InstanceNode): Context = {
      // These are the definitions that come from INSTANCE Naturals, Sequences, etc.
      // Declare operator aliases for them, which will be substituted with the operators by OpApplTranslator.
      // TODO: we do not process parameterized instances here
      var longPrefix = if (inst.getName == null) "" else inst.getName.toString
      longPrefix = if (instancePrefix == "") longPrefix else instancePrefix + "!" + longPrefix
      addAliasesOfBuiltins(ctx, longPrefix, inst.getModule)
    }

    node.getInstances.toList.foldLeft(newCtx)(eachInstance)
  }
}

object ModuleTranslator {

  def apply(sourceStore: SourceStore): ModuleTranslator = {
    new ModuleTranslator(sourceStore)
  }
}
