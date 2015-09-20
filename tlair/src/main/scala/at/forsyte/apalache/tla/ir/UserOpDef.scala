package at.forsyte.apalache.tla.ir

/**
 * A definition of a user-defined operator
 *
 * @author konnov
 */
class UserOpDef(val uid: Int,
             val uniqueName: String,
             val origin: Option[Origin],
             val params: List[ParamDecl])
  extends BaseEntry
