package at.forsyte.apalache.tla.assignments

import java.io._

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.UniqueDB
import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.{Map, Set}

object AlphaTLApTools {
  private def isCandTemplate( p_ex : TlaEx, p_var : Option[String] ) : Boolean = {
    p_ex match {
      case OperEx(
      TlaSetOper.in,
      OperEx(
      TlaActionOper.prime,
      NameEx( name )
      ),
      _
      ) => p_var.forall( _ == name )
      case _ => false
    }
  }

  def isCand( p_ex : TlaEx ) : Boolean = isCandTemplate( p_ex, None )

  def isVarCand( p_var : String, p_ex : TlaEx ) : Boolean = isCandTemplate( p_ex, Some( p_var ) )

  def findPrimes( p_ex : TlaEx ) : Set[String] = {
    p_ex match {
      case OperEx( TlaActionOper.prime, NameEx( name ) ) =>
        /* return */ Set( name )
      case OperEx( _, args@_* ) =>
        /* return */ args.map( findPrimes ).fold( Set[String]() ) {
        _ ++ _
      }
      case _ =>
        /* return */ Set[String]()
    }
  }

}

/**
  * Generates SMT constraints for assignment strategies.
  *
  * Assumes input in alpha-TLA+
  */
class AssignmentStrategyEncoder( val m_varSym : String = "b", val m_fnSym : String = "R" ) {

  private abstract class BoolFormula

  private object SMTtools {

    case class False( ) extends BoolFormula

    case class And( args : BoolFormula* ) extends BoolFormula

    case class Or( args : BoolFormula* ) extends BoolFormula

    case class Neg( arg : BoolFormula ) extends BoolFormula

    case class Implies( LHS : BoolFormula, RHS : BoolFormula ) extends BoolFormula

    case class Variable( id : Int ) extends BoolFormula

    case class LtFns( i : Int, j : Int ) extends BoolFormula // ( R( i ) < R( j ) )
    case class NeFns( i : Int, j : Int ) extends BoolFormula // ( R( i ) != R( j ) )

    def toSmt2( phi : BoolFormula ) : String = {
      phi match {
        case False() =>
          /* return */ "false" //"( false )"
        case And( args@_* ) =>
          /* return */ "( and %s )".format( args.map( toSmt2 ).mkString( " " ) )
        case Or( args@_* ) =>
          /* return */ "( or %s )".format( args.map( toSmt2 ).mkString( " " ) )
        case Neg( arg : BoolFormula ) =>
          /* return */ "( not %s )".format( toSmt2( arg ) )
        case Implies( lhs, rhs ) =>
          /* return */ "( => %s %s )".format( toSmt2( lhs ), toSmt2( rhs ) )
        case Variable( id : Int ) =>
          /* return */ "%s_%s".format( m_varSym, id )
        case LtFns( i : Int, j : Int ) =>
          /* return */ "( < ( %s %s ) ( %s %s ) )".format( m_fnSym, i, m_fnSym, j )
        case NeFns( i : Int, j : Int ) =>
          /* return */ "( not ( = ( %s %s ) ( %s %s ) ) )".format( m_fnSym, i, m_fnSym, j )
      }
    }

    def simplify( phi : BoolFormula ) : BoolFormula = {
      phi match {
        /**
          * Recursively simplify branches first.
          * If any branch is false, the whole formula is false.
          * It is important to recurse first,
          * since otherwise false-simplification would not propagate upward.
          */
        case And( args@_* ) =>
          val newargs = args.map( simplify )
          if ( newargs.contains( False() ) )
          /* return */ False()
          else
          /* return */ And( newargs : _* )

        /**
          * Recursively simplify, then drop all False() branches.
          * Afterwards, if the new tree has too few branches prune accordingly.
          */
        case Or( args@_* ) =>
          val newargs = args.map( simplify ).filterNot( _ == False() )
          newargs.size match {
            case 0 =>
              /* return */ False()
            case 1 =>
              /* return */ newargs.head
            case _ =>
              /* return */ Or( newargs : _* )
          }

        case _ =>
          /* return */ phi
      }
    }

  }

  private object Aliases {
    type seenType = Set[Int]
    type collocSetType = Set[(Int, Int)]
    type nonCollocSetType = collocSetType
    type deltaType = Map[String, BoolFormula]
    type frozenVarSetType = Set[String]
    type frozenType = Map[Int, frozenVarSetType]
    type recursionData =
      (seenType, collocSetType, nonCollocSetType, deltaType, frozenType)
    type staticAnalysisData =
      (seenType, collocSetType, deltaType, frozenType)

  }

  private def recursiveMainComputation( p_phi : TlaEx,
                                        p_vars : Set[String],
                                        p_frozenVarSet : Aliases.frozenVarSetType
                                      ) : Aliases.recursionData = {

    import SMTtools._
    import AlphaTLApTools._
    import Aliases._


    /** We name the default arguments to return at irrelevant terms  */
    val defaultMap = ( for {v <- p_vars} yield (v, False()) ).toMap
    val defaultArgs =
      (Set[Int](), Set[(Int, Int)](), Set[(Int, Int)](), defaultMap, Map[Int, Set[String]]())

    p_phi match {
      /** Recursive case, connectives */
      case OperEx( oper, args@_* ) if oper == TlaBoolOper.and || oper == TlaBoolOper.or => {

        /** First, process children */
        val processedChildArgs : Seq[recursionData] =
          args.map( recursiveMainComputation( _, p_vars, p_frozenVarSet ) )

        /** Compute parent delta from children */

        def deltaConnective( args : Seq[BoolFormula] ) = {
          if ( oper == TlaBoolOper.and ) Or( args : _* ) else And( args : _* )
        }

        val delta : deltaType =
          ( for {v <- p_vars} yield
            (v,
              deltaConnective(
                processedChildArgs.map(
                  /** Take the current delta_v. We know none of them are None by construction */
                  _._4( v )
                )
              )
            )
            ).toMap

        /**
          * The seen/colloc/noColloc sets are merely unions of their respective child sets.
          * In the case of the frozen mapping, the domains are disjoint so ++ suffices
          */
        val (seen, childCollocSet, childNoCollocSet, _, jointFrozen) =
          processedChildArgs.foldLeft(
            defaultArgs
          ) {
            ( a, b ) =>
              (
                a._1 ++ b._1,
                a._2 ++ b._2,
                a._3 ++ b._3,
                defaultArgs._4,
                a._5 ++ b._5 // Key sets disjoint by construction
              )
          }

        /** S is the set of all possible seen pairs */
        val S : collocSetType = for {x <- seen; y <- seen} yield (x, y)

        /**
          * At an AND node, all pairs not yet processed, that are not known to
          * be non-collocated, are collocated. At an OR branch, the opposite is true.
          */
        /* return */ oper match {
          case TlaBoolOper.and => (seen, S -- childNoCollocSet, childNoCollocSet, delta, jointFrozen)
          case TlaBoolOper.or => (seen, childCollocSet, S -- childCollocSet, delta, jointFrozen)
        }

      }

      /** Base case, assignment candidates */
      case OperEx( TlaSetOper.in, OperEx( TlaActionOper.prime, NameEx( name ) ), star ) => {
        val n : Int = p_phi.ID.id

        /** delta_v creates a fresh variable from the unique ID if name == v */
        val delta : deltaType =
          ( for {v <- p_vars}
            yield (v,
              if ( name == v )
                Variable( n )
              else
                False()
            )
            ).toMap

        /** At a terminal node, we know the exact values for the frozen sets */
        val starPrimes = findPrimes( star )
        val frozen : frozenType = Map( n -> (p_frozenVarSet ++ starPrimes) )
        /** A terminal node, is always collocated exactly with itself */
        val colloc : collocSetType = Set( (n, n) )
        val noColloc : nonCollocSetType = Set()
        /** Mark the node as seen */
        val seen : seenType = Set( n )

        /* return */ (seen, colloc, noColloc, delta, frozen)


      }

      /** Recursive case, quantifier */
      case OperEx( TlaBoolOper.exists, NameEx( _ ), star, subPhi ) => {
        /** All primes in the star expr. contribute to the frozen sets of subPhi */
        val starPrimes = findPrimes( star )
        val frozenVarSet = p_frozenVarSet ++ starPrimes

        /** Recurse on the child with a bigger frozen set */
        /* return */ recursiveMainComputation( subPhi, p_vars, frozenVarSet )

      }

      case OperEx( TlaControlOper.ifThenElse, star, thenExpr, elseExpr ) => {
        /** All primes in the star expr. contribute to the frozen sets of bothe subexpr. */
        val starPrimes = findPrimes( star )
        val frozenVarSet = p_frozenVarSet ++ starPrimes
        /** Recurse on both branches */
        val thenResults = recursiveMainComputation( thenExpr, p_vars, frozenVarSet )
        val elseResults = recursiveMainComputation( elseExpr, p_vars, frozenVarSet )

        /** Continue as with disjunction */
        val delta : deltaType =
          ( for {v <- p_vars} yield
            (v, And( thenResults._4( v ), elseResults._4( v ) ))
            ).toMap

        val seen = thenResults._1 ++ elseResults._1
        val childCollocSet = thenResults._2 ++ elseResults._2
        val jointFrozen = thenResults._5 ++ elseResults._5

        val S : collocSetType = for {x <- seen; y <- seen} yield (x, y)

        /* return */ (seen, childCollocSet, S -- childCollocSet, delta, jointFrozen)


      }

      case _ => defaultArgs

    }

  }

  private def staticAnalysis( p_phi : TlaEx,
                              p_vars : Set[String]
                            ) : Aliases.staticAnalysisData = {
    import SMTtools._
    val (seen, colloc, _, delta, frozen) =
      recursiveMainComputation( p_phi, p_vars, Set[String]() )
    /* return */ (seen, colloc, delta.map( pa => (pa._1, simplify( pa._2 )) ), frozen)
  }

  def apply( p_vars : Set[String],
             p_phi : TlaEx,
             p_fileName : Option[String] = None
           ) : String = {

    import SMTtools._
    import AlphaTLApTools._

    /** Extract the list of leaf ids, the collocated set, the delta mapping and the frozen mapping */
    val (seen, colloc, delta, frozen) = staticAnalysis( p_phi, p_vars )

    /**
      * We need two subsets of colloc, Colloc_\triangleleft for \tau_A
      * and Colloc_Vars for \tau_C
      */

    def minimalCoveringClash( i : Int, j : Int ) : Boolean = {
      val ex_i = UniqueDB( UID( i ) )
      val ex_j = UniqueDB( UID( j ) )

      p_vars.exists(
        v =>
          ex_i.exists( isVarCand( v, _ ) ) &&
            ex_j.exists( isVarCand( v, _ ) )
      )
    }

    def triangleleft( i : Int, j : Int ) : Boolean = {
      val ex_i = UniqueDB( UID( i ) )
      val ex_j = UniqueDB( UID( j ) )

      // unnecessary, by construction, seen/colloc only contains cand. IDs
      // ex_j.contains( isCand( _ ) ) &&
        p_vars.exists(
          v =>
            ex_i.exists( isVarCand( v, _ ) ) &&
              frozen( j ).contains( v )
        )
    }

    val colloc_Vars = colloc.filter( pa => minimalCoveringClash( pa._1, pa._2 ) )
    val colloc_tl = colloc.filter( pa => triangleleft( pa._1, pa._2 ) )

    // \theta_H unnecessary by construction
//    val notAsgnCand = seen.filterNot( i => UniqueDB( UID( i ) ).exists( isCand ) )
//
//    /** \theta_H */
//    val thetaHArgs = notAsgnCand.map( i => Neg( Variable( i ) ) )
//    val thetaH = thetaHArgs.map( toSmt2 )

    /** \theta_C^* */
    val thetaCStarArgs = delta.values
    val thetaCStar = thetaCStarArgs.map( toSmt2 )

    /** \theta^\E! */
    val thetaEArgs =
      for {(i, j) <- colloc_Vars if i < j}
        yield Neg( And( Variable( i ), Variable( j ) ) )
    val thetaE = thetaEArgs.map( toSmt2 )

    /** \theta_A^* */
    val thetaAStarArgs =
      for {(i, j) <- colloc_tl}
        yield Implies( And( Variable( i ), Variable( j ) ), LtFns( i, j ) )
    val thetaAStar = thetaAStarArgs.map( toSmt2 )

    /** \theta^inj */
    val thetaInjArgs = for {i <- seen; j <- seen if i < j} yield NeFns( i, j )
    val thetaInj = thetaInjArgs.map( toSmt2 )

    /** The constant/funciton declaration commands */
    val typedecls = seen.map( "( declare-fun %s_%s () Bool )".format( m_varSym, _ ) ).mkString( "\n" )
    val fndecls = "\n( declare-fun %s ( Int ) Int )\n".format( m_fnSym )

    /** Assert all of the constraints, as defined in \theta */
    val constraints = ( /*thetaH ++ */ thetaCStar ++ thetaE ++ thetaAStar ++ thetaInj ).map(
      str => "( assert %s )".format( str )
    ).mkString( "\n" )

    /** Partial return, sufficient for the z3 API */
    val ret = typedecls + fndecls + constraints

    /** Possibly produce standalone file */
    if ( p_fileName.nonEmpty ) {
      val logic = "( set-logic QF_UFLIA )\n"
      val end = "\n( check-sat )\n( get-model )\n( exit )"

      val pw = new PrintWriter( new File( p_fileName.get ) )
      pw.write( logic + ret + end )
      pw.close()

    }

    /* return */ ret
  }

}