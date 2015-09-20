package at.forsyte.apalache.tla.ir

/**
 * @param uid is a unique id,
 * @param uniqueName a unique name,
 * @param origin the origin
 * @param arity the arity of the parameter, i.e., the parameter is an operator
 * @param isLeibniz when true, then the parameter is Leibniz,
 *                  i.e., it respects substitution: A = B => F(A) = F(B).
 *
 * @see L. Lamport. TLA+2: a preliminary guide, p. 7. 15 Jan 2014.
 *
 * @author konnov
 */
class ParamDecl(val uid: Int,
            val uniqueName: String,
            val origin: Option[Origin],
            val arity: Int,
            val isLeibniz: Boolean)
  extends BaseEntry
