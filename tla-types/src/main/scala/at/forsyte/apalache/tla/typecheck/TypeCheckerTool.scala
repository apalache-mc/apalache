package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.annotations.{AnnotationStr, StandardAnnotations}
import at.forsyte.apalache.tla.lir
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.etc._
import at.forsyte.apalache.tla.typecheck.integration.{RecordingTypeCheckerListener, TypeRewriter}
import at.forsyte.apalache.tla.typecheck.parser.{DefaultType1Parser, Type1ParseError}
import com.typesafe.scalalogging.LazyLogging

/**
 * The API to the type checker. It first translates a TLA+ module into EtcExpr and then does the type checking.
 *
 * @author Igor Konnov
 */
class TypeCheckerTool(annotationStore: AnnotationStore, inferPoly: Boolean) extends LazyLogging {

  /**
   * Check the types in a module. All type checking events are sent to a listener.
   *
   * @param listener a listener of type checking events
   * @param module   a module to type check
   * @return the flag that indicates whether the module is well-typed
   */
  def check(listener: TypeCheckerListener, module: TlaModule): Boolean = {
    val varPool = new TypeVarPool()
    val aliases = loadTypeAliases(module.declarations)
    val toEtc = new ToEtcExpr(annotationStore, aliases, varPool)

    // Bool is the final expression in the chain of let-definitions
    val terminalExpr: EtcExpr = EtcConst(BoolT1())(BlameRef(UID.unique))

    // translate the whole TLA+ module into a long EtcExpr. Is not that cool?
    val topExpr =
      module.declarations.foldRight(terminalExpr) { case (decl, inScopeEx) =>
        toEtc(decl, inScopeEx)
      }

    // a hack: we wrap topExpr with LET-IN, so the type of topExpr is not overwritten
    def uniqueRef() = BlameRef(UID.unique)

    // generate a unique name for the root definition, to avoid clashes
    val rootName = "MODULE_%s_%d_APALACHE".format(module.name, System.currentTimeMillis())
    val rootExpr = EtcLet(rootName, EtcAbs(EtcConst(BoolT1())(uniqueRef()))(uniqueRef()), topExpr)(uniqueRef())

    val typeChecker = new EtcTypeChecker(varPool, inferPolytypes = inferPoly)
    // run the type checker
    val result = typeChecker.compute(listener, TypeContext.empty, rootExpr)
    result.isDefined
  }

  /**
   * Check the types in a module and, if the module is well-typed, produce a new module that attaches a type tag
   * to every expression and declaration in the module.
   *
   * @param tracker    a transformation tracker that is applied when expressions and declarations are tagged
   * @param listener   a listener to type checking events
   * @param defaultTag a function that returns a default type for UID, when type is missing
   * @param module     a module to type check
   * @return Some(newModule) if module is well-typed; None, otherwise
   */
  def checkAndTag(tracker: TransformationTracker, listener: TypeCheckerListener, defaultTag: UID => TypeTag,
      module: TlaModule): Option[TlaModule] = {
    val recorder = new RecordingTypeCheckerListener()
    if (!check(new MultiTypeCheckerListener(listener, recorder), module)) {
      None
    } else {
      val transformer = new TypeRewriter(tracker, defaultTag)(recorder.toMap)
      val taggedDecls = module.declarations.map(transformer(_))
      Some(new TlaModule(module.name, taggedDecls))
    }
  }

  private def loadTypeAliases(declarations: Seq[TlaDecl]): Map[String, TlaType1] = {
    var aliases = Map[String, lir.TlaType1]()

    for (decl <- declarations) {
      annotationStore.get(decl.ID).foreach { annotations =>
        annotations.filter(_.name == StandardAnnotations.TYPE_ALIAS).foreach { annot =>
          annot.args match {
            case Seq(AnnotationStr(text)) =>
              aliases += parseTypeAlias(decl.name, aliases, text)

            case args =>
              throw new TypingInputException(
                  s"Unexpected annotation alias in front of ${decl.name}: " + args.mkString(", "))
          }
        }
      }
    }

    aliases
  }

  // parse type from its text representation
  private def parseTypeAlias(where: String, aliases: Map[String, TlaType1], text: String): (String, TlaType1) = {
    try {
      DefaultType1Parser.parseAlias(aliases, text)
    } catch {
      case e: Type1ParseError =>
        logger.error("Parsing error in the alias annotation: " + text)
        throw new TypingInputException(s"Parser error in type alias of $where: ${e.msg}")
    }
  }
}
