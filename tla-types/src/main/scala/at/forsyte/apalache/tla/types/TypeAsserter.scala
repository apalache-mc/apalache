package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools.{BoolFormula, False}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator

class TypeAsserter( val specLimits: SpecLimits, private val smtVarGen : SmtVarGenerator ) {

  private val enum = specLimits.getEnumeration

  implicit def singleton( bf : BoolFormula ) : Seq[BoolFormula] = Seq( bf )

  private var observedFields: Map[SmtIntVariable, Set[String]] = Map.empty

  def getObservedFields : Map[SmtIntVariable, Set[String]] = observedFields

  def typeAssert( t : SmtDatatype, tau : TlaType, c : TypeContext ): Seq[BoolFormula] = tau match {
    case tv : TypeVar => c.get( tv ).map( x => Seq( Eql( t, x ) ) ).getOrElse( Seq( False() ) )
    case IntT => Eql( t, int )
    case StrT => Eql( t, str )
    case BoolT => Eql( t, bool )
    case SetT( tauPrime ) =>
      val tPrime = smtVarGen.getFresh
      Eql(t, set(tPrime)) +: typeAssert( tPrime, tauPrime, c)
    case SeqT( tauPrime ) =>
      val tPrime = smtVarGen.getFresh
      Eql(t, seq(tPrime)) +: typeAssert( tPrime, tauPrime, c)
    case FunT( domT, cdmT ) =>
      val List( tDom, tCdm ) = smtVarGen.getNFresh( 2 )
      Eql( t, fun( tDom, tCdm ) ) +: typeAssert( tDom, domT, c ) ++: typeAssert( tCdm, cdmT, c )
    case TupT( taus@_* ) =>
      val l = taus.length
      val ts = smtVarGen.getNFresh( specLimits.maxIndex )
      val size = SmtKnownInt( l )

      // zip ignores elements of the larger collection (presumably ts) with no matching pair
      val constraints = taus.zip( ts ).flatMap {
        case (tauj, tj) => typeAssert( tj, tauj, c )
      }

      Eql( t, tup( size, ts ) ) +: constraints

    case OperT( TupT( taus@_* ), cdmT ) =>
      val l = taus.length
      val ts = smtVarGen.getNFresh( specLimits.maxIndex )
      val size = SmtKnownInt( l )

      // zip ignores elements of the larger collection (presumably ts) with no matching pair
      val constraints = taus.zip( ts ).flatMap {
        case (tauj, tj) => typeAssert( tj, tauj, c )
      }

      val tprime = smtVarGen.getFresh

      Eql( t, oper( tup( size, ts ), tprime ) ) +: typeAssert( tprime, cdmT, c ) ++: constraints
    case SparseTupT( tsMap ) =>
      val ts = smtVarGen.getNFresh( specLimits.maxIndex )
      val maxKey = tsMap.keySet.max

      val constraints = ts.zipWithIndex withFilter {
        case (_, j) => tsMap.contains( j )
      } flatMap {
        case (tij, j) => typeAssert( tij, tsMap(j), c )
      }
      val sizeVar = smtVarGen.getFreshInt

      Eql( t, tup( sizeVar, ts ) ) +: ge( sizeVar, maxKey ) +: constraints

    case RecT( tsMap ) =>
      val ts = smtVarGen.getNFresh( specLimits.maxNumFields )
      val fields = tsMap.keySet
      val id = smtVarGen.getFreshInt

      // remember fields for recovery
      observedFields += ( id -> fields )

      val constraints = ts.zipWithIndex withFilter {
        case (_, j) => fields.contains( enum.getVal( j ) )
      } flatMap {
        case (tij, j) => typeAssert( tij, tsMap( enum.getVal( j ) ), c )
      }

      Eql( t, rec( id, ts ) ) +: constraints
    case PolyOperT( _, op ) =>
      typeAssert( t, op, c )
  }

}
