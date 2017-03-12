package at.forsyte.apalache.tla.obsolete.ir

/**
 * A TLA+ module.
 *
 * @author konnov
 */
class Module(val origin: Origin,
              val uniqueName: String,
              val constants: List[UserOpDecl],
              val variables: List[UserOpDecl],
              val operators: List[UserOpDef],
              val assumptions: List[Assumption],
              val theorems: List[Theorem])
