package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx}

/**
 * <p>Many processing methods transform a TLA+ expression into another TLA+ expression. Sometimes, we also
 * transform declarations. To record these changes, we have introduced this listener. The clients who are willing
 * to track changes should implement their listener and register it with a TransformationFactory.</p>
 *
 * @author Igor Konnov
 */
trait TransformationListener {
  def onTransformation(originalEx: TlaEx, newEx: TlaEx): Unit

  def onDeclTransformation(originalDecl: TlaDecl, newDecl: TlaDecl): Unit
}
