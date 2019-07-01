package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A general expression transformation. Although it just implements the function trait, it can be easily decorated
  * with additional behavior.
  *
  * @author Igor Konnov
 */
trait ExprTransformer extends Function1[TlaEx, TlaEx]
