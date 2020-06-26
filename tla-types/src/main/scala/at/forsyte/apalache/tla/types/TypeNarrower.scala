package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.types.smt.IndexEvaluator

object TypeNarrower {
  type FieldMap = Map[Int, Set[String]]
}

/**
  * When using SMT to find record types, sometimes the computed records contain spurious
  * fields. TypeNarrower uses input information to retain only the
  * fields for which an explicit constraint exists.
  */
class TypeNarrower( observed : Map[SmtIntVariable, Set[String]], idxEval : IndexEvaluator ) {
  import TypeNarrower._

  /**
    * We record `observed` by SMT variables, but in the model evaluation some of these SMTInt variables
    * collapse into the same integer (as defined by `idxEval`) so we make a new map that records
    * fields belonging to an evaluated record identifier.
    */
  private val fieldMap : FieldMap = observed.foldLeft( Map.empty[Int, Set[String]] ) {
        case (partialMap, (SmtIntVariable( i ), s)) =>
          val idxVal = idxEval.getValue( i )
          val newSet = partialMap.getOrElse( idxVal, Set.empty ) ++ s
          partialMap + ( idxVal -> newSet )
  }

  def narrow( t : TlaType, i : Int ) : TlaType = t match {
    case RecT( tmap ) =>
      RecT( tmap filterKeys fieldMap.getOrElse( i, Set.empty ).contains )
    case _ => t
  }

}
