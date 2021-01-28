package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools

abstract class SmtDatatype

sealed case class SmtIntVariable(id: Long)
sealed case class SmtTypeVariable(id: Long) extends SmtDatatype

object int extends SmtDatatype
object str extends SmtDatatype
object bool extends SmtDatatype
sealed case class set(st: SmtDatatype) extends SmtDatatype
sealed case class seq(sq: SmtDatatype) extends SmtDatatype
sealed case class tup(j: SmtIntVariable) extends SmtDatatype
sealed case class rec(r: SmtIntVariable) extends SmtDatatype
sealed case class fun(arg: SmtDatatype, res: SmtDatatype) extends SmtDatatype
sealed case class oper(oarg: SmtDatatype, ores: SmtDatatype) extends SmtDatatype

sealed case class Eql(lhs: SmtDatatype, rhs: SmtDatatype)
    extends SmtTools.BoolFormula
sealed case class hasField(v: SmtIntVariable, s: String, t: SmtDatatype)
    extends SmtTools.BoolFormula
sealed case class hasIndex(v: SmtIntVariable, i: Int, t: SmtDatatype)
    extends SmtTools.BoolFormula
// sizeOf(i) = j
sealed case class sizeOfEql(i: SmtIntVariable, j: Int)
    extends SmtTools.BoolFormula
