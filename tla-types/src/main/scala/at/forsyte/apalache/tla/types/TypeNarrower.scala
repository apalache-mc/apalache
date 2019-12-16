package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.types.smt.IndexEvaluator

object TypeNarrower {
  type FieldMap = Map[Int, Set[String]]
}

/**
  * When using SMT to find record types, sometimes the computed records contain spurious
  * fields. TypeNarrower uses input information (hasField constraints) to retain only the
  * fields for which an explicit constraint exists.
  */
class TypeNarrower( constraints : Traversable[hasField], eqs : IndexEvaluator ) {
  import TypeNarrower._

  private val fieldMap : FieldMap = constraints.foldLeft( Map.empty[Int, Set[String]] ) {
    case (partialMap, hasField( SmtIntVariable( i ), s, _ )) =>
      val valOf = eqs.getValue( i )
      val newVal = partialMap.getOrElse( valOf, Set.empty ) + s
      partialMap + ( valOf -> newVal )
  }

  def narrow( t : TlaType, i : Int ) : TlaType = t match {
    case RecT( tmap ) =>
      RecT( tmap filterKeys fieldMap.getOrElse( i, Set.empty ).contains )
    case _ => t
  }
}
