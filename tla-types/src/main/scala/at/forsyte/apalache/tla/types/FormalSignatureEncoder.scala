package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools.BoolFormula
import at.forsyte.apalache.tla.lir.{FormalParam, OperFormalParam, SimpleFormalParam, TlaOperDecl}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator

sealed case class SigTriple( opType : SmtDatatype, paramTypes : List[SmtDatatype], constraints : Seq[BoolFormula] )

/**
  * Generates formal signature constraints for user-defined operators.
  *
  * Formal signatures introduce type variables for every parameter and for the return type,
  * making sure that OperFormalParam parameters are assigned oper-type variables
  */
class FormalSignatureEncoder( private val smtVarGen: SmtVarGenerator ) {
  /**
    * Generates a formal signature of an operator, given the operator's formal parameters
    *
    * The signature is a triple SigTriple( t, a, phi ), where
    * phi is the operator's type (usually oper(tup(_),_)), a is a vector of return and argument values
    * (to be used as an argument for the template call) and phi is a collection of constraints
    */
  def sig( fParams: List[FormalParam] ) : SigTriple = fParams match {
    case Nil =>
      val f = smtVarGen.getFresh
      SigTriple( f, List( f ), Seq.empty )
    case params =>
      val f = smtVarGen.getFresh
      val i = smtVarGen.getFreshInt
      val pts = params map paramType
      val paramDTs = f +: ( pts map { _.t } )
      val constraints = sizeOfEql( i, params.length ) +: ( pts.zipWithIndex flatMap {
        case (ReductionResult( ti, phii ), j) =>
          hasIndex( i, j, ti ) +: phii
      } )
      SigTriple( oper( i, f ), paramDTs, constraints )
  }

  /**
    * Computes the parameter type (and associated constraints) for the given FormalParam
    *
    * For SimpleFormalParam, the type is a fresh variable and the constraints are empty
    * For OperFormalParam, the type is an oper( tup(_), _ ) type, and the constraints
    * specify the tuple size and the type variables for each index
    */
  def paramType( fp : FormalParam ) : ReductionResult = fp match {
    case _ : SimpleFormalParam =>
      ReductionResult( smtVarGen.getFresh, Seq.empty )
    case OperFormalParam( _, arity ) =>
      val i = smtVarGen.getFreshInt
      val f +: fs = smtVarGen.getNFresh( arity + 1 )
      ReductionResult(
        oper( i, f ),
        sizeOfEql( i, arity ) +: ( fs.zipWithIndex map { case (fj, j) =>
          hasIndex( i, j, fj )
        } )
      )
  }
}
