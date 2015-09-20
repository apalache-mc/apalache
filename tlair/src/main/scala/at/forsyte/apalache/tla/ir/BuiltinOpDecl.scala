package at.forsyte.apalache.tla.ir

/**
 * A built-in operator declaration.
 *
 * @author konnov
 */
class BuiltinOpDecl(val uid: Int,
              val uniqueName: String,
              val origin: Option[Origin],
              val params: List[ParamDecl])
    extends BaseEntry {

}
