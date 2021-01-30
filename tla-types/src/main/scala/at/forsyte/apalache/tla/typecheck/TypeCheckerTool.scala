package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.lir.{TlaModule, UID}
import at.forsyte.apalache.tla.typecheck.etc._

/**
 * The API to the type checker. It first translates a TLA+ module into EtcExpr and then does the type checking.
 *
 * @author Igor Konnov
 */
class TypeCheckerTool(annotationStore: AnnotationStore, inferPoly: Boolean) {
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
}
