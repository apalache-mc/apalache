package at.forsyte.apalache.tla.ir

/**
 * A TLA+ module.
 *
 * @author konnov
 */
class Module(val origin: Origin,
              val uniqueName: String,
              val consts: List[UserOpDecl],
              val vars: List[UserOpDecl],
              val ops: List[UserOpDef],
              val assumptions: List[Assumption],
              val theorems: List[Theorem])
