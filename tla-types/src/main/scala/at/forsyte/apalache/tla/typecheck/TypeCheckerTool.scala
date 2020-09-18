package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{TlaModule, UID}
import at.forsyte.apalache.tla.typecheck.etc._

/**
  * The API to the type checker. It first translates a TLA+ module into EtcExpr and then does the type checking.
  *
  * @author Igor Konnov
  */
class TypeCheckerTool {
  def check(listener: TypeCheckerListener, module: TlaModule): Boolean = {
    // TODO: remember to type check the assumptions!

    // translate the whole TLA+ module into a long EtcExpr. Is not that cool?
    val toEtc = new ToEtcExpr
    // Bool is the final expression in the chain of let-definitions
    val terminalExpr: EtcExpr = EtcConst(BoolT1()) (BlameRef(UID.unique))
    val rootExpr =
      module.operDeclarations.foldRight(terminalExpr) {
        case (decl, inScopeEx) => toEtc(decl, inScopeEx)
      }
    // run the type checker
    val result = new EtcTypeChecker().compute(listener, TypeContext.empty, rootExpr)
    result.isDefined
  }
}
