package at.forsyte.apalache.tla.lir

import scalaz.Scalaz._
import scalaz._

import scala.reflect.Manifest

// TODO: @Igor: please move it to the package *.process
// @Igor: this looks like a mini-functional language inside Scala. It is an unnecessary abstraction. Do not use it.
object RecursiveProcessor {

  object DefaultFunctions {
    def naturalTermination[T] : T => Boolean = _ => false

    def noOp[T] : T => Unit = _ => ()

    def identity[T] : T => T = x => x

    def equality[T] : (T, T) => Boolean = _ == _

    // TODO: Igor @ 01.07.2019: why all of a sudden we are doing fixpoint computations on doubles?
    def epsEquality[T]( eps : Double, d : (T, T) => Double )( x : T, y : T ) : Boolean = d( x, y ) <= eps

    def childCollect[T1, T2](
                              p_initial : T2,
                              p_collectFun : (T2, T2) => T2
                            )(
                              p_parent : T1,
                              p_children : Traversable[T2]
                            ) : T2 =
      p_children.fold( p_initial )( p_collectFun )

    def subtypeHasChildren[T1, T2 <: T1 : Manifest]( p_ex : T1 ) : Boolean = p_ex match {
      case e : T2 => true
      case _ => false
    }

    def tlaExHasChildren : TlaEx => Boolean = subtypeHasChildren[TlaEx, OperEx]

    def subtypeGetChildren[T1, T2 <: T1 : Manifest](
                                                     p_select : T2 => Traversable[T1]
                                                   )(
                                                     p_ex : T1
                                                   ) : Traversable[T1] = p_ex match {
      case e : T2 => p_select( e )
      case _ => Traversable.empty[T1]
    }

    def tlaExGetChildren : TlaEx => Traversable[TlaEx] = subtypeGetChildren[TlaEx, OperEx]( _.args )

    def tlaExTransformChildren( p_ex : TlaEx, p_children : Traversable[TlaEx] ) : TlaEx =
      p_ex match {
        case OperEx( oper, args@_* ) =>
          if ( args == p_children ) // in case of no-op, do not reconstruct OperEx
            p_ex
          else OperEx( oper, p_children.toSeq : _* )
        case _ => p_ex
      }

    def ignoreChildren[T1, T2](
                                p_parentFun : T1 => T2
                              )(
                                p_parent : T1,
                                p_children : Traversable[T2]
                              ) : T2 =
      p_parentFun( p_parent )
  }

  private val _recursionLimit = 3000

  def computeFixpoint[T](
                          p_fun : T => T,
                          p_termniationCheck : (T, T) => Boolean = DefaultFunctions.equality[T]
                        )(
                          p_val : T
                        )(
                          implicit recursionLimit : Int = _recursionLimit
                        ) : Option[T] = {
    if ( recursionLimit <= 0 ) None
    else {
      val app = p_fun( p_val )
      if ( p_termniationCheck( app, p_val ) ) Some( app )
      else Some( app ) flatMap {
        computeFixpoint( p_fun, p_termniationCheck )( _ )( recursionLimit - 1 )
      }
    }
  }

  def computeS[S, T1, T2](
                           p_terminationCheck : T1 => Boolean,
                           p_terminalExFun : T1 => State[S, T2],
                           p_nonTerminalExFun : T1 => State[S, T2],
                           p_hasRelevantChildren : T1 => Boolean,
                           p_getChildren : T1 => Traversable[T1],
                           p_childUnification : (T1, Traversable[T2]) => State[S, T2]
                         )(
                           p_ex : T1
                         ) : State[S, T2] =
    if ( p_terminationCheck( p_ex ) ) {
      p_terminalExFun( p_ex )
    }

    else if ( p_hasRelevantChildren( p_ex ) ) {
      val recFun = computeS(
        p_terminationCheck,
        p_terminalExFun,
        p_nonTerminalExFun,
        p_hasRelevantChildren,
        p_getChildren,
        p_childUnification
      ) _

      val x = p_getChildren(p_ex).toList traverseS recFun
      x flatMap { p_childUnification( p_ex, _ ) }
    }
    else {
      p_nonTerminalExFun( p_ex )
    }

  def compute[T1, T2](
                       p_terminationCheck : T1 => Boolean,
                       p_terminalExFun : T1 => T2,
                       p_nonTerminalExFun : T1 => T2,
                       p_hasRelevantChildren : T1 => Boolean,
                       p_getChildren : T1 => Traversable[T1],
                       p_childUnification : (T1, Traversable[T2]) => T2
                     )(
                       p_ex : T1
                     ) : T2 =
    if ( p_terminationCheck( p_ex ) )
      p_terminalExFun( p_ex )
    else if ( p_hasRelevantChildren( p_ex ) ) {
      val childVals : Traversable[T2] =
        p_getChildren( p_ex ) map compute(
          p_terminationCheck,
          p_terminalExFun,
          p_nonTerminalExFun,
          p_hasRelevantChildren,
          p_getChildren,
          p_childUnification
        )
      p_childUnification( p_ex, childVals )
    }
    else p_nonTerminalExFun( p_ex )

  def globalProperty[T](
                         p_propertyFun : T => Boolean,
                         p_hasRelevantChildren : T => Boolean,
                         p_getChildren : T => Traversable[T]
                       ) : T => Boolean =
    compute[T, Boolean](
      DefaultFunctions.naturalTermination[T],
      p_propertyFun,
      p_propertyFun,
      p_hasRelevantChildren,
      p_getChildren,
      ( p, chd ) => p_propertyFun( p ) && chd.forall( identity )
    )

  def computeFromTlaEx[T](
                           p_terminationCheck : TlaEx => Boolean,
                           p_terminalExFun : TlaEx => T,
                           p_nonTerminalExFun : TlaEx => T,
                           p_childUnification : (TlaEx, Traversable[T]) => T
                         ) : TlaEx => T =
    compute[TlaEx, T](
      p_terminationCheck,
      p_terminalExFun,
      p_nonTerminalExFun,
      DefaultFunctions.tlaExHasChildren,
      DefaultFunctions.tlaExGetChildren,
      p_childUnification
    )

  def globalTlaExProperty( p_propertyFun : TlaEx => Boolean ) : TlaEx => Boolean =
    globalProperty[TlaEx](
      p_propertyFun,
      DefaultFunctions.tlaExHasChildren,
      DefaultFunctions.tlaExGetChildren
    )

  def transformTlaEx(
                      p_terminationCheck : TlaEx => Boolean,
                      p_terminalExFun : TlaEx => TlaEx,
                      p_nonTerminalExFun : TlaEx => TlaEx
                    ) : TlaEx => TlaEx =
    computeFromTlaEx[TlaEx](
      p_terminationCheck,
      p_terminalExFun,
      p_nonTerminalExFun,
      ( par, chds ) => {
        val newEx = DefaultFunctions.tlaExTransformChildren( par, chds )
        if ( p_terminationCheck( newEx ) )
          p_terminalExFun( newEx )
        else p_nonTerminalExFun( newEx )
      }
    )

  def traverseTlaEx(
                     p_terminationCheck : TlaEx => Boolean,
                     p_terminalExFun : TlaEx => Unit,
                     p_nonTerminalExFun : TlaEx => Unit,
                     p_intermediateNodeFun : TlaEx => Unit
                   ) : TlaEx => Unit =
    computeFromTlaEx[Unit](
      p_terminationCheck,
      p_terminalExFun,
      p_nonTerminalExFun,
      DefaultFunctions.ignoreChildren( p_intermediateNodeFun )
    )

  def traverseEntireTlaEx(
                           p_exFun : TlaEx => Unit
                         ) : TlaEx => Unit =
    traverseTlaEx(
      DefaultFunctions.naturalTermination,
      DefaultFunctions.noOp,
      p_exFun,
      p_exFun
    )
}
