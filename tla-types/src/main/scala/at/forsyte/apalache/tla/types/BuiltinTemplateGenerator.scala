package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.smt.SmtTools.{And, Or}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator

/**
  * Generates templates for built-in TLA+ operators.
  *
  * @param smtVarGen - generates fresh SMT variables on demand
  */
class BuiltinTemplateGenerator( private val smtVarGen : SmtVarGenerator ) {
  private val sigGen    = new SignatureGenerator
  private val reduction = new TypeReduction( smtVarGen )

  /**
    * Generates a template from an OperEx.
    *
    * The function is passed an entire OperEx, because there exist built-in
    * operators, the arity of which is not fixed. From the entire expression, we
    * can generate the correct template, by analyzing not just the number of arguments, but
    * also their values, in the case of record types (where the field names need to be known)
    */
  def makeTemplate( ex : OperEx ) : Template = {
    case e +: ts =>
      val sigs = sigGen.getPossibleSignatures( ex )
      // In general, overloaded operators can have >1 potential signature
      val subTemplates = sigs map { case PolyOperT( tVars, OperT( TupT( xs@_* ), y ) ) =>
        // We create fresh SMT variables, which hold the concrete types of the type parameters
        // in this operator call
        val m : TypeContext = tVars.map(
          _ -> smtVarGen.getFresh
        ).toMap

        // We can't define a Template class to have a variable number of arguments
        // in its apply(...) method, so we can only enforce run-time arity checks
        assert( ts.length == xs.length )

        // By definition, concat all sub-deltas
        val conjConstraints =
          xs.zip( ts ).foldLeft( reduction.delta( e, y, m ) ) {
            case (cs, (xi, ti)) => reduction.delta( ti, xi, m ) ++: cs
          }

        // Enforce actual identity on EXCEPT (used with record types)
        // EXCEPT underspecifies the return type, because it has to exactly match the input type,
        // even if not all fields are explicitly updated
        val exceptOpt = ex.oper match {
          case TlaFunOper.except =>
            Some( Eql( e, ts.head ) )
          case _ => None
        }

        And( exceptOpt ++: conjConstraints : _* )
      }
      // In most cases, subTemplates is a singleton, so there's no need to wrap it in an Or
      subTemplates match {
        case h +: Nil => h
        case _ => Or( subTemplates : _* )
      }
    case Nil =>
      throw new IllegalArgumentException("Templates must accept at least 1 argument.")
  }

}
