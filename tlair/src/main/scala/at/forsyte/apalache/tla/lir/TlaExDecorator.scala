package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.TlaOper


// TODO: REMOVE?
trait TlaExDecorator

// TODO: REMOVE?
trait ToggleFlag extends TlaExDecorator {
  protected var toggled = false

  def isToggled : Boolean = toggled

  def setTo( p_val : Boolean ) : Unit = toggled = p_val

  def enable() : Unit = toggled = true

  def disable() : Unit = toggled = false

  def toggle() : Unit = toggled = !toggled

}

// TODO: REMOVE?
class FlaggedOperEx( oper : TlaOper, args : TlaEx* ) extends OperEx( oper, args : _* ) with ToggleFlag

// TODO: REMOVE?
class FlaggedNameEx( name : String ) extends NameEx( name ) with ToggleFlag

// TODO: REMOVE?
class FlaggedValEx( value : TlaValue ) extends ValEx( value ) with ToggleFlag


object lir {
//  implicit def dropFlagOper( p_flagged : FlaggedOperEx ) : OperEx =
//    OperEx( p_flagged.oper, p_flagged.args:_* )
//
//  implicit def dropFlagName( p_flagged : FlaggedNameEx ) : NameEx =
//    NameEx( p_flagged.name )
//
//  implicit def dropFlagVal( p_flagged : FlaggedValEx ) : ValEx =
//    ValEx( p_flagged.value )

  // TODO: REMOVE?
  implicit def addFlagOper( p_opEx : OperEx ) : FlaggedOperEx =
    new FlaggedOperEx( p_opEx.oper, p_opEx.args:_* )

  // TODO: REMOVE?
  implicit def addFlagName( p_nmEx : NameEx ) : FlaggedNameEx =
    new FlaggedNameEx( p_nmEx.name )

  // TODO: REMOVE?
  implicit def addFlagVal( p_nmEx : ValEx ) : FlaggedValEx =
    new FlaggedValEx( p_nmEx.value )

}