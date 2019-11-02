package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}

/**
  * <p>A class that implements LanguagePrecondition checks, whether a TLA+ expression, or a whole module,
  * fits into a fragment of TLA+. For instance, FlatLanguagePred expects that all user operators have been inlined.</p>
  *
  * <p>The most reasonable usage for a language predicate is to use in conjunction with LanguageWatchdog,
  * which fails immediately, once an expression is outside of the expected fragment.
  * This feature addresses issue #68.</p>
  *
  * @author Igor Konnov
  */
trait LanguagePred {
  def isExprOk(ex: TlaEx): Boolean

  def isModuleOk(mod: TlaModule): Boolean
}
