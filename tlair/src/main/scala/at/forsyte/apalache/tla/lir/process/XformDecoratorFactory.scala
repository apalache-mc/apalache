package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * An abstract interface to transformer decorators.
  *
  * @author Igor Konnov
  */
trait XformDecoratorFactory {
  def decorate(xformer: TlaEx => TlaEx): XformDecoratorFun
}
