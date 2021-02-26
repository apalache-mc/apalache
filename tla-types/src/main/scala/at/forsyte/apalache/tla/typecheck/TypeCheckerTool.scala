package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.{TlaModule, UID}
import at.forsyte.apalache.tla.typecheck.etc._
import at.forsyte.apalache.tla.typecheck.integration.{RecordingTypeCheckerListener, TypeRewriter}

/**
 * The API to the type checker. It first translates a TLA+ module into EtcExpr and then does the type checking.
 *
 * @author Igor Konnov
 */
class TypeCheckerTool(annotationStore: AnnotationStore, inferPoly: Boolean) {

  /**
   * Check the types in a module. All type checking events are sent to a listener.
   *
   * @param listener a listener of type checking events
   * @param module   a module to type check
   * @return the flag that indicates whether the module is well-typed
   */
  def check(listener: TypeCheckerListener, module: TlaModule): Boolean = {
    val varPool = new TypeVarPool()
    val toEtc = new ToEtcExpr(annotationStore, varPool)

    // Bool is the final expression in the chain of let-definitions
    val terminalExpr: EtcExpr = EtcConst(BoolT1())(BlameRef(UID.unique))

    // translate the whole TLA+ module into a long EtcExpr. Is not that cool?
    val rootExpr =
      module.declarations.foldRight(terminalExpr) { case (decl, inScopeEx) =>
        toEtc(decl, inScopeEx)
      }

    // run the type checker
    val result = new EtcTypeChecker(varPool, inferPolytypes = inferPoly).compute(listener, TypeContext.empty, rootExpr)
    result.isDefined
  }

  /**
   * Check the types in a module and, if the module is well-typed, produce a new module that attaches a type tag
   * to every expression and declaration in the module.
   *
   * @param tracker  a transformation tracker that is applied when expressions and declarations are tagged
   * @param listener a listener to type checking events
   * @param module   a module to type check
   * @return Some(newModule) if module is well-typed; None, otherwise
   */
  def checkAndTag(tracker: TransformationTracker, listener: TypeCheckerListener,
      module: TlaModule): Option[TlaModule] = {
    val recorder = new RecordingTypeCheckerListener()
    if (!check(new MultiTypeCheckerListener(listener, recorder), module)) {
      None
    } else {
      val transformer = new TypeRewriter(tracker)(recorder.toMap)
      val taggedDecls = module.declarations.map(transformer(_))
      Some(new TlaModule(module.name, taggedDecls))
    }
  }
}
