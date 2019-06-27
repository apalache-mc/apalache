package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A function decorator that wraps every function call out = xform(input)
  * with a call to the subscribed TransformationListener objects.
  *
  * @param xformer a function that transforms an input expression to an output expression
  *
  * @author Jure Kukovec, Igor Konnov
  */
class BroadcastXformDecoratorFun(listeners: List[TransformationListener],
                                 xformer: TlaEx => TlaEx) extends XformDecoratorFun {
  /**
    * Apply the transformation function to the input and call the transformation listeners.
    *
    * @param input an input expression
    * @return the output expression
    */
  def apply(input: TlaEx): TlaEx = {
    val output = xformer(input)
    for (l <- listeners) {
      l.onTransformation(input, output)
    }
    output
  }
}