package at.forsyte.apalache.tla.ir

/**
 * A declaration of a user-defined operator, e.g., of a variable.
 * UserOpDecl differs from UserOpDef in that the former does not have a body.
 *
 * @author konnov
 */
class UserOpDecl(val uid: Int,
                 val uniqueName: String,
                 val origin: Option[Origin],
                 val arity: Int,
                 val kind: Kind.Value)
  extends BaseEntry