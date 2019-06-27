package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A trait for a transformation decorator, which acts as a function.
  *
  * @author Jure Kukovec, Igor Konnov
  */
trait XformDecoratorFun extends Function1[TlaEx, TlaEx] {
}
