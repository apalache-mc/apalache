package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, Typed}
import at.forsyte.apalache.tla.lir.oper.TlaOper

sealed case class BuildInstruction(oper: TlaOper, typeCmp: typeComputation) {
  def build(args: TlaEx*): TlaEx = {
    val typeTag = Typed(typeCmp(args))
    OperEx(oper, args: _*)(typeTag)
  }
}
