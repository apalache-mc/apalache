package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools

/**
  * SmtDatatype represents an intermediate layer of abstraction between the TlaType
  * and the eventual solver-dependent SMT datatype implementation
  */
abstract class SmtDatatype {
  override def toString : String = TypePrinter( this )
}

/**
  * SmtVariable is either an integer of represents a TlaType
  */
trait SmtVariable
trait SmtInt

sealed case class SmtIntVariable( id: Int ) extends SmtVariable with SmtInt {
  override def toString : String = s"${Names.intVarSymb}($id)"
}
sealed case class SmtTypeVariable( id: Int ) extends SmtDatatype with SmtVariable

sealed case class SmtKnownInt( i: Int ) extends SmtInt

/**
  * See paper for a discussion on the datatype.
  *
  * We don't need a representation of varT, since no signature-based constraints define it
  */
object int extends SmtDatatype
object str extends SmtDatatype
object bool extends SmtDatatype
sealed case class set( st: SmtDatatype ) extends SmtDatatype
sealed case class seq( sq: SmtDatatype ) extends SmtDatatype
sealed case class tup( size: SmtInt, idxs: Seq[SmtDatatype] ) extends SmtDatatype
sealed case class rec( id: SmtIntVariable, fields: Seq[SmtDatatype] ) extends SmtDatatype
sealed case class fun( arg: SmtDatatype, res: SmtDatatype ) extends SmtDatatype
sealed case class oper( domTup: tup, ret: SmtDatatype ) extends SmtDatatype

// Eql was not defined in SmtTools.BoolFormula
sealed case class Eql( lhs: SmtDatatype, rhs: SmtDatatype  ) extends SmtTools.BoolFormula
sealed case class ge( intVar: SmtIntVariable, minSize: Int ) extends SmtTools.BoolFormula
