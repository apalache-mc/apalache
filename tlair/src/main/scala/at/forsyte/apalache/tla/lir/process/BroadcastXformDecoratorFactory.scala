package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir.TlaEx

import scala.collection.mutable

/**
  * A factory that creates instances of BroadcastXformDecorator.
  * The idea is to use this factory, in order to let the expression transformers to track the updates.
  *
  * @author Igor Konnov
  */
class BroadcastXformDecoratorFactory extends XformDecoratorFactory {
  /**
    * Transformation listeners that are passed to the new instances of BroadcastXformDecorator.
    */
  var listeners: mutable.MutableList[TransformationListener] = mutable.MutableList()

  /**
    * Create a decorator for a specific expression transformer.
    *
    * @param xformer an expression transformer
    * @return a decorated function
    */
  def decorate(xformer: TlaEx => TlaEx): BroadcastXformDecoratorFun = {
    new BroadcastXformDecoratorFun(listeners.toList, xformer)
  }
}
