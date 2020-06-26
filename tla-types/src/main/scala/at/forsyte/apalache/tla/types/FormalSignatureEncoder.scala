package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools.{BoolFormula, False}
import at.forsyte.apalache.tla.lir.{FormalParam, OperFormalParam, SimpleFormalParam, TlaOperDecl}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator

sealed case class SigTriple( opType : SmtDatatype, paramTypes : List[SmtDatatype], constraints : Seq[BoolFormula] )

/**
  * Generates formal signature constraints for user-defined operators.
  *
  * Formal signatures introduce constraints for every parameter and for the return type,
  * making sure that OperFormalParam parameters are assigned oper-type variables
  */
class FormalSignatureEncoder( val specLimits: SpecLimits, private val smtVarGen: SmtVarGenerator ) {
  /**
    * Generates a formal signature of an operator, given the operator's formal parameters
    *
    * The signature takes as arguments 2 + k variables, where k is the operator arity, the 1st representing
    * the operator type, the 2nd the return type and the following k representing the types of the k arguments passed
    * to the operator
    */

  def sig( fParams: List[FormalParam] ) : Seq[SmtDatatype] => Seq[BoolFormula] = {
    case o +: f +: ts =>
      val k = fParams.length

      // Sanity check, |ts| = |fParams|
      assert( ts.length == k )

      val size = SmtKnownInt( k )
      // Instead of making M variables and k equalities, we just make
      // M-k variables and re-use the first k
      val kAlt = specLimits.maxIndex - k
      // Sanity check
      assert( kAlt >= 0)
      val fs = ts ++: smtVarGen.getNFresh( kAlt )

      val constraints = ts.zip(fParams) flatMap {
        case (tj, pj) => paramType( pj )( tj )
      }

      Eql( o, oper( tup( size, fs ), f ) ) +: constraints

    case _ =>
      throw new IllegalArgumentException("Signatures must accept at least 2 arguments.")
  }

  /**
    * Computes the parameter type (and associated constraints) for the given FormalParam
    */
  def paramType( p : FormalParam )( f: SmtDatatype  ) : Seq[BoolFormula] = p match {
    case _ : SimpleFormalParam => Seq.empty
    case OperFormalParam( _, arity ) =>
      val ts = smtVarGen.getNFresh( specLimits.maxIndex )
      val t = smtVarGen.getFresh
      val size = SmtKnownInt( arity )
      Seq( Eql( f, oper( tup( size, ts ), t ) ) )
  }

}
