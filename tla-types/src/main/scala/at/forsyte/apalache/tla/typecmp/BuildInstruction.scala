package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, Typed}
import at.forsyte.apalache.tla.lir.oper.TlaOper

sealed case class BuildInstruction(oper: TlaOper, typeCmp: typeComputation) {
  def build(args: TlaEx*): TlaEx = {
    typeCmp(args) match {
      case Left(err) => throw err
      case Right(typeRes) =>
        OperEx(oper, args: _*)(Typed(typeRes))
    }
  }
}
