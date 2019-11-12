package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools.BoolFormula
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator

/**
  * The result of a reduction is a pair of a type-representation, t,  and constraitns, phi.
  */
sealed case class ReductionResult( t : SmtDatatype, phi : Seq[BoolFormula] )

/**
  * TypeReduction allows us to construct the SMT representation of a given
  * TlaType, together with possible additional constraints, e.g. tuple index or record field
  * information.
  */
class TypeReduction( private val smtVarGen : SmtVarGenerator ) {
  def reduce( tau : TlaType, m : TypeContext ) : ReductionResult = tau match {
    case t : TypeVar => ReductionResult( m( t ), Seq.empty )
    case IntT => ReductionResult( int, Seq.empty )
    case StrT => ReductionResult( str, Seq.empty )
    case BoolT => ReductionResult( bool, Seq.empty )
    case SetT( tauPrime ) =>
      val ReductionResult( v, phi ) = reduce( tauPrime, m )
      ReductionResult( set( v ), phi )
    case SeqT( tauPrime ) =>
      val ReductionResult( v, phi ) = reduce( tauPrime, m )
      ReductionResult( seq( v ), phi )
    case FunT( domT, cdmT ) =>
      val ReductionResult( v1, phi1 ) = reduce( domT, m )
      val ReductionResult( v2, phi2 ) = reduce( cdmT, m )
      ReductionResult( fun( v1, v2 ), phi1 ++ phi2 )
    case OperT( domT, cdmT ) =>
      val ReductionResult( v1, phi1 ) = reduce( domT, m )
      val ReductionResult( v2, phi2 ) = reduce( cdmT, m )
      ReductionResult( oper( v1, v2 ), phi1 ++ phi2 )
    case TupT( ts@_* ) =>
      val l = ts.length
      val results = ts map {
        reduce( _, m )
      }
      val tupIdx = smtVarGen.getFreshInt
      val constraints = results.zipWithIndex.flatMap {
        case (ReductionResult( ti, phii ), i) =>
          hasIndex( tupIdx, i, ti ) +: phii
      }
      val phi = sizeOfEql( tupIdx, l ) +: constraints
      ReductionResult( tup( tupIdx ), phi )
    case RecT( tsMap ) =>
      val recIdx = smtVarGen.getFreshInt
      val constraints = tsMap.toSeq flatMap {
        case ( k, v ) =>
          val ReductionResult( t, phi ) = reduce( v, m )
          hasField( recIdx, k, t ) +: phi
      }
      ReductionResult( rec( recIdx ), constraints )
    case SparseTupT( tsMap ) =>
      val tupIdx = smtVarGen.getFreshInt
      val constraints = tsMap.toSeq flatMap {
        case ( k, v ) =>
          val ReductionResult( t, phi ) = reduce( v, m )
          hasIndex( tupIdx, k, t ) +: phi
      }
      ReductionResult( tup( tupIdx ), constraints )
    case PolyOperT( _, op ) =>
      reduce( op, m )
  }

  /**
    * The delta function, as defined in the paper.
    *
    * Creates the constraints capturing the property that f represents the SMT encoding of the type tau.
    */
  def delta( f : SmtDatatype, tau : TlaType, m : TypeContext ) : Seq[BoolFormula] = {
    val ReductionResult( v, phi ) = reduce( tau, m )
    Eql( f, v ) +: phi
  }


}
