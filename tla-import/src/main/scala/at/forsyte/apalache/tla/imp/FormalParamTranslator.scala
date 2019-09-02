package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.oper.FixedArity
import at.forsyte.apalache.tla.lir.{FormalParam, OperFormalParam, SimpleFormalParam}
import tla2sany.semantic.FormalParamNode

/**
  * A translator of FormalParamNode.
  *
  * @author konnov
  */
class FormalParamTranslator {
  def translate(param: FormalParamNode): FormalParam = {
    if (param.getArity == 0) {
      SimpleFormalParam(param.getName.toString.intern())
    } else {
      OperFormalParam(param.getName.toString.intern(), param.getArity)
    }
  }
}

object FormalParamTranslator {
  private val singleton: FormalParamTranslator = new FormalParamTranslator()


  def apply(): FormalParamTranslator = {
    // as our objects do not have state, we can always return a singleton here
    singleton
  }
}
