package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.assignments.transformations.InlineFactory
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.control.LetInOper
import at.forsyte.apalache.tla.lir.db.{BodyDB, BodyDBFactory}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{RecursiveTransformation, Transformation, TransformationListener}
import com.google.inject.Singleton

/**
  * Object responsible for pre-processing input before it is passed to the
  * [[at.forsyte.apalache.tla.assignments.AssignmentStrategyEncoder encoder]].
  */
@Singleton
class Transformer {
  // Igor: this class does a lot of things. Write comments on what the outcome is.
  // Igor: Does this class have to be stateful?
  //
  // Igor: Let's find a better name for this class.
  //
  // Igor @ 27/12/2017: converted from a singleton to a class.
  // Let Guice take care of instantiating the object rightly.

  /**
    * Extracts information about operators' bodies and stores it for later substitution.
    *
    * @param p_decls  Collection of declarations. All instances that are not [[TlaOperDecl]] are ignored.
    * @param p_bodyDB Mapping from operator names to their bodies.
    */
  def extract( p_decls : TlaDecl*
             )
             ( implicit p_bodyDB : BodyDB
             ) : Unit = {
    BodyDBFactory.makeDBFromDecls( p_decls, p_bodyDB )
  }

  /**
    * Extracts variable declarations.
    *
    * @param p_decls Collection of declarations. All instances that are not [[TlaVarDecl]] are ignored.
    * @return A set of variable names.
    */
  def getVars( p_decls : TlaDecl* ) : Set[String] = {
    p_decls.withFilter( _.isInstanceOf[TlaVarDecl] ).map( _.name ).toSet
  }

  /**
    * Replaces all occurrences of operator application with their bodies until a fixpoint is reached.
    *
    * Occurrences of [[TlaRecOperDecl]] are not expanded.
    *
    * @param p_expr   Input expression.
    * @param p_bodyDB Mapping from operator names to their bodies. Should not contain recursive operators.
    * @param p_srcDB  Mapping from replaced expressions to their originals.
    * @return A new [[TlaEx]], where all operator applications, for operators from `p_bodyDB`, have been
    *         replaced by their bodies (with parameters substituted by the arguments).
    */
  def inlineAll(
                 p_expr : TlaEx
               )
               (
                 implicit p_bodyDB : BodyDB,
                 p_srcDB : TransformationListener
               ) : TlaEx = {
    InlineFactory(p_bodyDB, p_srcDB).InlineAll(p_expr)
//    OperatorHandler.unfoldMax( p_expr, p_bodyDB, p_srcDB )
  }

  /**
    * Recursively replaces UNCHANGED (x1,...,xn) by x1' \in {x1} /\ ... /\ xn' \in {xn}
    *
    * @param p_ex  Input expression.
    * @param srcDB Mapping from replaced expressions to their originals.
    * @return A new [[TlaEx]], where all occurrences of UNCHANGED have been replaced
    *         by their equivalent alpha-TLA+ compatible forms.
    */
  def unchangedExplicit(
                         p_ex : TlaEx
                       )(
                         implicit srcDB : TransformationListener
                       ) : TlaEx = {

    def exFun( ex : TlaEx ) : TlaEx = {
      /** Make x' \in {x} expression */
      def lambda( x : TlaEx ) =
        Builder.in( Builder.prime( x ), Builder.enumSet( x ) )

      ex match {
        case OperEx( TlaActionOper.unchanged, arg ) =>

          /** Consider UNCHANGED x
            * and UNCHANGED (x,y,...)
            * */
          arg match {
            case OperEx( TlaFunOper.tuple, args@_* ) =>
              Builder.and( args.map( lambda ) : _* )
            case NameEx( _ ) => lambda( arg )
            case _ => ex
          }
        case _ => ex
      }
    }

    // Temporary, until this class gets deleted
    new RecursiveTransformation( new Transformation( exFun, srcDB ) )(p_ex)
  }

  /**
    * Substitutes applications of operators declared in a LET-IN statement by their bodies.
    *
    * Undefined behaviour on recursive operators.
    *
    * @see inlineAll
    * @param p_ex Input expression
    * @param srcDB Mapping from replaced expressions to their originals.
    * @return A new [[TlaEx]], where all occurrences of operator applications,
    *         for operators declared in a LET expression,
    *         have been replaced by their bodies (with parameters substituted by arguments).
    */
  def explicitLetIn(
                     p_ex : TlaEx
                   )(
                     implicit srcDB : TransformationListener
                   ) : TlaEx = {
    def exFun( ex : TlaEx ) : TlaEx = {
      ex match {
        case OperEx( oper : LetInOper, body ) =>
          /** Make a fresh temporary DB, store all decls inside */
          val bodyDB = BodyDBFactory.makeDBFromDecls( oper.defs )

          /** inline as if operators were external */
          explicitLetIn( inlineAll( body )( bodyDB, srcDB ) )( srcDB )
        case _ => ex
      }
    }

    val ret = RecursiveProcessor.transformTlaEx(
      RecursiveProcessor.DefaultFunctions.naturalTermination,
      exFun,
      exFun
    )(p_ex)
    srcDB.onTransformation( p_ex, ret)
    ret
//
//    val oldret = OperatorHandler.replaceWithRule( p_ex, exFun, srcDB )
//    oldret
  }

  /**
    * Recursively replaces x' = y by x' \in {y}
    *
    * @param p_ex  Input expression.
    * @param srcDB Mapping from replaced expressions to their originals.
    * @return A new [[TlaEx]], where all occurrences of x' = y have been replaced
    *         by x' \in {y}.
    */
  def rewriteEQ(
                 p_ex : TlaEx
               )
               (
                 implicit srcDB : TransformationListener
               ) : TlaEx = {
    def lambda( tlaEx : TlaEx ) : TlaEx = {
      tlaEx match {
        case OperEx( TlaOper.eq, lhs@OperEx( TlaActionOper.prime, _ ), rhs ) =>
          OperEx( TlaSetOper.in, lhs, OperEx( TlaSetOper.enumSet, rhs ) )
        case e@_ => e
      }
    }

    // Temporary, until this class gets deleted
    new RecursiveTransformation( new Transformation( lambda, srcDB ) )(p_ex)
  }

  //
  // TODO : develop flags for sanitize, to know which transformations to perform
  //

  /**
    * Performs several transformations in sequence.
    *
    * Currently, performs the following:
    *   1. [[inlineAll]]
    *   1. [[rewriteEQ]]
    *   1. [[unchangedExplicit]]
    * @param p_expr Input expression.
    * @param bodyDB Operator body mapping, for unfolding.
    * @param listener a listener to transformations.
    * @return Expression obtained after applying the sequence of transformations.
    */
  def sanitize(
                p_expr : TlaEx
              )
              (
                implicit bodyDB : BodyDB,
                listener : TransformationListener
              ) : TlaEx = {
    val inlined = inlineAll( p_expr )( bodyDB, listener )

    val explicitLI = explicitLetIn( inlined )( listener )

    val eqReplaced = rewriteEQ( explicitLI )(listener )

    /* val ucReplaced = */ unchangedExplicit( eqReplaced )( listener )

  }

  // Igor: normally, the most important methods come first in a class declaration.
  // Igor: why is this method declared with apply? What is special about it?
  /**
    * Performs [[extract]], followed by [[sanitize]] and identification.
    * @param p_expr Input expression.
    * @param p_decls Collection of declared operators.
    * @param p_bodyDB Mapping from operator names to their bodies. Should not contain recursive operators.
    * @param p_listener  a listener to transformations.
    * @return None, if [[sanitize]] fails, otherwise contains the sanitized expression.
    */
  def apply( p_expr : TlaEx,
             p_decls : TlaDecl*
           )(
             implicit p_bodyDB : BodyDB,
             p_listener : TransformationListener
           ) : Option[TlaEx] = {
    extract( p_decls : _* )( p_bodyDB )
    val san = sanitize( p_expr )( p_bodyDB, p_listener )
    if ( san.isNull ) None
    else Some( san )
  }

}
