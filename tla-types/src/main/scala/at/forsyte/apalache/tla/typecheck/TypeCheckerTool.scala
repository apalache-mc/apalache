package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.annotations.{AnnotationStr, StandardAnnotations}
import at.forsyte.apalache.io.typecheck.parser.Type1ParseError
import at.forsyte.apalache.tla.lir
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.etc._
import at.forsyte.apalache.tla.typecheck.integration.{RecordingTypeCheckerListener, TypeRewriter}
import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import com.typesafe.scalalogging.LazyLogging

/**
 * The API to the type checker. It first translates a TLA+ module into EtcExpr and then does the type checking.
 *
 * @author
 *   Igor Konnov
 */
class TypeCheckerTool(annotationStore: AnnotationStore, inferPoly: Boolean, useRows: Boolean) extends LazyLogging {

  /**
   * Check the types in a module. All type checking events are sent to a listener.
   *
   * @param listener
   *   a listener of type checking events
   * @param module
   *   a module to type check
   * @return
   *   the flag that indicates whether the module is well-typed
   */
  def check(listener: TypeCheckerListener, module: TlaModule): Boolean = {
    val maxTypeVar = findMaxUsedTypeVar(module)
    val varPool = new TypeVarPool(maxTypeVar + 1)
    val aliasSubstitution = loadTypeAliases(module.declarations)
    val toEtc = new ToEtcExpr(annotationStore, aliasSubstitution, varPool, useRows)

    // Bool is the final expression in the chain of let-definitions
    val terminalExpr: EtcExpr = EtcConst(BoolT1)(BlameRef(UID.unique))

    // translate the whole TLA+ module into a long EtcExpr. Is not that cool?
    val topExpr =
      module.declarations.foldRight(terminalExpr) { case (decl, inScopeEx) =>
        toEtc(decl, inScopeEx)
      }

    // a hack: we wrap topExpr with LET-IN, so the type of topExpr is not overwritten
    def uniqueRef() = BlameRef(UID.unique)

    // generate a unique name for the root definition, to avoid clashes
    val rootName = "MODULE_%s_%d_APALACHE".format(module.name, System.currentTimeMillis())
    val rootExpr = EtcLet(rootName, EtcAbs(EtcConst(BoolT1)(uniqueRef()))(uniqueRef()), topExpr)(uniqueRef())

    val typeChecker = new EtcTypeChecker(varPool, inferPolytypes = inferPoly)
    // run the type checker
    val result = typeChecker.compute(listener, TypeContext.empty, rootExpr)
    result.isDefined
  }

  /**
   * Check the types in a module and, if the module is well-typed, produce a new module that attaches a type tag to
   * every expression and declaration in the module.
   *
   * @param tracker
   *   a transformation tracker that is applied when expressions and declarations are tagged
   * @param listener
   *   a listener to type checking events
   * @param defaultTag
   *   a function that returns a default type for UID, when type is missing
   * @param module
   *   a module to type check
   * @return
   *   Some(newModule) if module is well-typed; None, otherwise
   */
  def checkAndTag(
      tracker: TransformationTracker,
      listener: TypeCheckerListener,
      defaultTag: UID => TypeTag,
      module: TlaModule): Option[TlaModule] = {
    val recorder = new RecordingTypeCheckerListener()
    if (!check(new MultiTypeCheckerListener(listener, recorder), module)) {
      None
    } else {
      val transformer = new TypeRewriter(tracker, defaultTag)(recorder.toMap)
      val taggedDecls = module.declarations.map(transformer(_))
      Some(TlaModule(module.name, taggedDecls))
    }
  }

  private def loadTypeAliases(declarations: Seq[TlaDecl]): ConstSubstitution = {
    var aliases = Map[String, lir.TlaType1]()

    // extract all aliases from the annotations
    for (decl <- declarations) {
      annotationStore.get(decl.ID).foreach { annotations =>
        annotations.filter(_.name == StandardAnnotations.TYPE_ALIAS).foreach { annot =>
          annot.args match {
            case Seq(AnnotationStr(text)) =>
              aliases += parseTypeAlias(decl.name, text)

            case args =>
              throw new TypingInputException(
                  s"Unexpected annotation alias in front of ${decl.name}: " + args.mkString(", "), decl.ID)
          }
        }
      }
    }

    // Aliases can refer to one another. Substitute the aliases until we arrive at a fixpoint.
    ConstSubstitution(aliases).closure()
  }

  // parse type from its text representation
  private def parseTypeAlias(where: String, text: String): (String, TlaType1) = {
    try {
      DefaultType1Parser.parseAlias(text)
    } catch {
      case e: Type1ParseError =>
        logger.error("Parsing error in the alias annotation: " + text)
        throw new TypingInputException(s"Parser error in type alias of $where: ${e.msg}", UID.nullId)
    }
  }

  // Find the maximum index used in type tags of a module.
  // We need this index to initialize the variable pool,
  // so the fresh type variables do not conflict with the old type variables.
  private def findMaxUsedTypeVar(module: TlaModule): Int = {
    def findInTag: TypeTag => Int = {
      case Typed(tt: TlaType1) =>
        val used = tt.usedNames
        if (used.isEmpty) -1 else used.max

      case _ => -1
    }

    def findInEx: TlaEx => Int = {
      // only LET-IN expressions may introduce fresh type variables, as we have let polymorphism
      case LetInEx(body, defs @ _*) =>
        defs.map(findInDecl).foldLeft(findInEx(body))(Math.max)

      case OperEx(_, args @ _*) =>
        args.map(findInEx).foldLeft(-1)(Math.max)

      case _ =>
        -1
    }

    def findInDecl: TlaDecl => Int = {
      case d @ TlaOperDecl(_, _, body) =>
        Math.max(findInEx(body), findInTag(d.typeTag))

      case d =>
        findInTag(d.typeTag)
    }

    module.declarations.map(findInDecl).foldLeft(-1)(Math.max)
  }
}
