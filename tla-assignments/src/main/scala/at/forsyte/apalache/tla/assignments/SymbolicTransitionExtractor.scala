package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._

/**
  * Performs the complete procedure of finding symbolic transitions from the TLA+ implementation.
  *
  * @see [[AssignmentStrategyEncoder]], [[SMTInterface]], [[SymbTransGenerator]]
  *
  * Jure, 28.8.19: Should symbolic transitions track their origin?
  */
object SymbolicTransitionExtractor extends TypeAliases {

  /**
    * Body lookup.
    *
    * @param p_opName Name of the TLA+ operator declaration.
    * @param decls    Collection of declarations to be searched.
    * @return The body of the operator declaration, if it is an element of the collection, otherwise NullEx.
    */
  protected def findBodyOf( p_opName : String, decls : Seq[TlaDecl] ) : TlaEx = {
    decls.find {
      _.name == p_opName
    }.withFilter( _.isInstanceOf[TlaOperDecl] ).map( _.asInstanceOf[TlaOperDecl].body ).getOrElse( NullEx )
  }

  /**
    * Point of access method.
    *
    * Throws [[AssignmentException]] if:
    *   a. The operator `p_nextName` is not a member of `p_decls`
    *   a. No assignment strategy exists for `p_nextName`
    *
    * @param decls    Declarations to be considered. Must include variable declarations and all of the
    *                   non-recursive operators appearing in the spec.
    * @param nextName The name of the operator defining the transition relation.
    * @return A collection of symbolic transitions, if they can be extracted.
    *
    */
  def apply( decls : Seq[TlaDecl],
             nextName : String = "Next"
           ) : Seq[SymbTrans] = {
    /** Extract variable declarations */
    val vars = decls.withFilter( _.isInstanceOf[TlaVarDecl] ).map( _.name ).toSet

    /** Extract transition relation */
    val phi = findBodyOf( nextName, decls )

    val stratEncoder = new AssignmentStrategyEncoder()

    /** Generate an smt encoding of the assignment problem to pass to the SMT solver */
    val spec = stratEncoder( vars, phi )

    /** Get strategy from the solver */
    val strat = ( new SMTInterface() ) ( spec, stratEncoder.m_varSym )

    /** Throw if no strat. */
    if ( strat.isEmpty )
      throw new AssignmentException(
        "No assignment strategy found for %s".format( nextName )
      )

    /** From a strategy, compute symb. trans. */
    val transitions = ( new SymbTransGenerator() ) ( phi, strat.get )

    transitions
  }

}
