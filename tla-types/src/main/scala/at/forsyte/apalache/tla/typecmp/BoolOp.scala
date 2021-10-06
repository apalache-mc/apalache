package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

object BoolOp {
  def andCmp: pureTypeComputation = { args =>
    if (args.forall(_ == BoolT1()))
      BoolT1()
    else
      throwMsg(s"${TlaBoolOper.and.name} expects arguments of type (Bool*), found: (${args.mkString(",")})")
  }

}
