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

sealed case class SmtIntVariable( id: Int ) extends SmtVariable {
  override def toString : String = s"${Names.intVarSymb}($id)"
}
sealed case class SmtTypeVariable( id: Int ) extends SmtDatatype with SmtVariable

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
sealed case class tup( j: SmtIntVariable ) extends SmtDatatype
sealed case class rec( r: SmtIntVariable ) extends SmtDatatype
sealed case class fun( arg: SmtDatatype, res: SmtDatatype ) extends SmtDatatype
sealed case class oper( i: SmtIntVariable, ores: SmtDatatype ) extends SmtDatatype

/**
  * We include abstractions of the functions used in the constraints
  *
  * Note that e.g. hasField(a,b,c) gets translated to [hasField(a,b) && atField(a,b) = c] at
  * the SMT level, to allow for easier solution recovery from the SMT models
  */
sealed case class hasField( v: SmtIntVariable, s: String, t: SmtDatatype ) extends SmtTools.BoolFormula
sealed case class hasIndex( v: SmtIntVariable, i: Int, t: SmtDatatype  ) extends SmtTools.BoolFormula
// sizeOf(i) = j
sealed case class sizeOfEql( i: SmtIntVariable, j: Int ) extends SmtTools.BoolFormula

// Eql was not defined in SmtTools.BoolFormula
sealed case class Eql( lhs: SmtDatatype, rhs: SmtDatatype  ) extends SmtTools.BoolFormula
