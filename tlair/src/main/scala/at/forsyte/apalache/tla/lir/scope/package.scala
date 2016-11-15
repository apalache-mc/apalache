package at.forsyte.apalache.tla.lir.scope

import at.forsyte.apalache.tla.lir._

/**
 * The scopes of TLA+ expressions.
 */
abstract class ScopeSymbol {
  def name: String
}

// declare a for LET a = ... IN...
case class ScopeLetVariable(param: SimpleFormalParam) extends ScopeSymbol {
  override def name: String = param.name
}

// declare x for \forall x \in X. ...
case class ScopeBoundVariable(param: SimpleFormalParam) extends ScopeSymbol {
  override def name: String = param.name
}

// an operator parameter
case class ScopeFormalParameter(param: FormalParam) extends ScopeSymbol {
  override def name: String = param.name
}

// a variable
case class ScopeVariable(tlaVar: TlaVarDecl) extends ScopeSymbol {
  override def name: String = tlaVar.name
}

// a constant
case class ScopeConstant(const: TlaConstDecl) extends ScopeSymbol {
  override def name: String = const.name
}

// an operator definition
case class ScopeOper(operDef: TlaOperDecl) extends ScopeSymbol {
  override def name: String = operDef.name
}

// a lookup exception
class SymbolNotFoundException(val msg: String) extends RuntimeException

/**
 * A scope in which constants and variables are declared.
 */
trait TlaScope {
  def add(sym: ScopeSymbol): Unit

  def remove(name: String): Unit

  def exists(name: String): Boolean

  def lookup(name: String): ScopeSymbol // throws SymbolNotFoundException
}

