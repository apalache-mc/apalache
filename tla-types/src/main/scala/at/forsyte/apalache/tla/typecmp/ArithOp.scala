package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.lir.oper.TlaArithOper

object ArithOp {
  def plusCmp: pureTypeComputation = {
    case Seq(IntT1(), IntT1()) => IntT1()
    case args =>
      throwMsg(s"${TlaArithOper.plus.name} expects arguments of type (Int,Int), found: (${args.mkString(",")})")
  }

}
