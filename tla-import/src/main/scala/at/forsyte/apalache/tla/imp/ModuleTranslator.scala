package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import com.typesafe.scalalogging.LazyLogging
import tla2sany.semantic.{InstanceNode, ModuleNode, OpDefNode}

import scala.collection.JavaConverters._

/**
 * Translate a tla2tools ModuleNode to a TlaModule.
 *
 * @author konnov
 */
class ModuleTranslator(sourceStore: SourceStore, annotationStore: AnnotationStore) extends LazyLogging {
  private val annotationExtractor = new AnnotationExtractor(annotationStore)

  def translate(node: ModuleNode): TlaModule = {
    var context = node.getConstantDecls.toList.foldLeft(Context()) { (ctx, node) =>
      val decl = TlaConstDecl(node.getName.toString)
      sourceStore.add(decl.ID, SourceLocation(node.getLocation))
      annotationExtractor.parseAndSave(decl.ID, node)
      ctx.push(DeclUnit(decl))
    }
    context = node.getVariableDecls.toList.foldLeft(context) { (ctx, node) =>
      val decl = TlaVarDecl(node.getName.toString)
      sourceStore.add(decl.ID, SourceLocation(node.getLocation))
      annotationExtractor.parseAndSave(decl.ID, node)
      ctx.push(DeclUnit(decl))
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
        case d: DeclUnit =>
          throw new SanyImporterException("Duplicate definition: " + d.name)

        case NoneUnit() =>
          // translate only the user-defined operators, skip the aliases
          val decl = NullOpDefTranslator(sourceStore, ctx).translate(opDef)
          ctx.push(DeclUnit(decl))

        case _ => ctx // skip the aliases
      }
    }

    context = opDefs.foldLeft(context)(eachOpDefFirstPass)

    // second pass: produce the actual operator bodies and do substitution
    for (opDef <- opDefs) {
      context.lookup(opDef.getName.toString) match {
        case DeclUnit(decl: TlaOperDecl) =>
          val lookupPrefix = opDef.getName.toString.split("!").dropRight(1) // find the instance names
          // the expression translator should lookup using the lookupPrefix
          val adjustedContext = context.setLookupPrefix(lookupPrefix.toList)
          val defTranslator = OpDefTranslator(sourceStore, annotationStore, adjustedContext)
          val updatedDecl = defTranslator.translate(opDef)
          // copy the structures from the updated definition
          decl.isRecursive = updatedDecl.isRecursive
          decl.body = updatedDecl.body
          sourceStore.find(updatedDecl.ID) match {
            case None =>
              // to guarantee that we do not forget the source location, fail fast
              throw new SanyImporterException("No source location for: " + updatedDecl.name)
            case Some(loc) =>
              sourceStore.add(decl.ID, loc)
          }
          annotationStore.get(updatedDecl.ID).foreach { annotations =>
            annotationStore += decl.ID -> annotations
          }

          // TODO(igor) temporary bugfix for the issue #130. Remove as soon as it is fixed in tla2tools.
          // https://github.com/informalsystems/apalache/issues/130
          workaroundMarkRecursive(Set(decl), decl.body)

        case _ => () // XXX: do something?
      }
    }

    // translate assumptions after the operator definitions, as the assumptions may use the operators
    context = node.getAssumptions.toList.foldLeft(context) { (ctx, node) =>
      val decl = AssumeTranslator(sourceStore, annotationStore, ctx).translate(node)
      sourceStore.add(decl.ID, SourceLocation(node.getLocation))
      ctx.push(DeclUnit(decl))
    }

    // filter out the aliases, keep only the user definitions and declarations
    val actualDefs = context.declarations.collect({ case DeclUnit(d) => d })
    new TlaModule(node.getName.toString, actualDefs)
  }

  private def addAliasesOfBuiltins(
      ctx: Context, instancePrefix: String, node: ModuleNode
  ): Context = {
    // declare a library definition as an operator alias
    def subDef(
        ctx: Context, modName: String, alias: String, opDefNode: OpDefNode
    ): Context = {
      val opName = opDefNode.getName.toString.intern()
      var newCtx = ctx
      StandardLibrary.libraryOperators.get((modName, opName)).collect { case oper =>
        newCtx = newCtx.push(OperAliasUnit(alias, oper))
      }
      StandardLibrary.globalOperators.get(opName).collect { case oper =>
        newCtx = newCtx.push(OperAliasUnit(alias, oper))
      }
      StandardLibrary.libraryValues.get((modName, opName)).collect { case value =>
        newCtx = newCtx.push(ValueAliasUnit(alias, value))
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
    var newCtx = node.getOpDefs.foldLeft(ctx) { (c, d) =>
      subDef(c, modName, alias(d), d)
    }

    // add aliases for the definitions in the modules that this one EXTENDS
    val extendedModules = node.getExtendedModuleSet.asScala.toList
    newCtx = extendedModules.foldLeft(newCtx) { (c, m) =>
      addAliasesOfBuiltins(c, instancePrefix, m)
    }

    // add aliases for the definitions that come from the INSTANCE declarations
    def eachInstance(ctx: Context, inst: InstanceNode): Context = {
      // These are the definitions that come from INSTANCE Naturals, Sequences, etc.
      // Declare operator aliases for them, which will be substituted with the operators by OpApplTranslator.
      // TODO: we do not process parameterized instances here
      var longPrefix = if (inst.getName == null) "" else inst.getName.toString
      longPrefix =
        if (instancePrefix == "") longPrefix
        else instancePrefix + "!" + longPrefix
      addAliasesOfBuiltins(ctx, longPrefix, inst.getModule)
    }

    node.getInstances.toList.foldLeft(newCtx)(eachInstance)
  }

  /**
   * This is a temporary bugfix for the issue 130: https://github.com/informalsystems/apalache/issues/130
   * TODO(igor) Once it is fixed in SANY, remove this method. This method does not detect mutually recursive operators,
   * but I have never seen mutual recursion in TLA+.
   *
   * @param declared the set of names that have been introduced at higher levels.
   */
  private def workaroundMarkRecursive(
      declared: Set[TlaOperDecl], ex: TlaEx
  ): Unit = {
    ex match {
      case NameEx(name) =>
        declared.find(_.name == name).foreach {
          // the operator is used inside its own definition, mark as recursive
          d =>
            if (!d.isRecursive) {
              logger.warn(
                  s"WORKAROUND #130: labelling operator $name as recursive, though SANY did not tell us so."
              )
              d.isRecursive = true
            }
        }

      case LetInEx(body, defs @ _*) =>
        for (d <- defs) {
          // go inside the definition and mark it recursive if needed
          workaroundMarkRecursive(declared + d, d.body)
        }

        // traverse the body for nested LET-IN definitions
        workaroundMarkRecursive(declared, body)

      case OperEx(_, args @ _*) =>
        // traverse the arguments for nested LET-IN definitions
        args.foreach(workaroundMarkRecursive(declared, _))

      case _ => () // a terminal expression
    }
  }
}

object ModuleTranslator {

  def apply(sourceStore: SourceStore, annotationStore: AnnotationStore): ModuleTranslator = {
    new ModuleTranslator(sourceStore, annotationStore)
  }
}
