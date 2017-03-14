package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{FormalParam, SimpleFormalParam}
import tla2sany.semantic.FormalParamNode

/**
  * A translator of FormalParamNode.
  *
  * @author konnov
  */
class FormalParamTranslator {
  def translate(param: FormalParamNode): FormalParam = {
    assert(0 == param.getArity)
    SimpleFormalParam(param.getName.toString.intern())
  }
}

object FormalParamTranslator {
  private val singleton: FormalParamTranslator = new FormalParamTranslator()


  def apply(): FormalParamTranslator = {
    // as our objects do not have state, we can always return a singleton here
    singleton
  }
}
