package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.{TlaConstDecl, TlaDecl, TlaVarDecl}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator

/**
  * Creates a global name context
  */
class GlobalBindingBuilder( private val gen : SmtVarGenerator ) {
  /**
    * If `primeConsistency` is true, the type of each variable v will be forced to match
    * the type of its prime, v', (they will point at the exact same SMT variable)
    */
  def build( decls : Traversable[TlaDecl], primeConsistency : Boolean ) : GlobalBinding =
    ( decls flatMap {
      case TlaVarDecl( n ) =>
        val vn = gen.getFresh
        val vnPrime =
          if ( primeConsistency ) vn
          else gen.getFresh
        List( n -> vn, s"$n'" -> vnPrime )
      case TlaConstDecl( c ) => List( c -> gen.getFresh )
      case _ => List.empty
    } ).toMap
}
