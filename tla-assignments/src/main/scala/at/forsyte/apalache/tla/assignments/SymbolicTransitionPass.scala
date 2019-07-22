package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.process.DeclarationModifiers
import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMap

/**
  * Performs the complete procedure of finding symbolic transitions from the TLA+ implementation.
  *
  * @see [[AssignmentStrategyEncoder]], [[SMTInterface]], [[SymbTransGenerator]]
  */
class SymbolicTransitionPass( private val m_bodyMap : BodyMap,
                              private val m_srcDB : TransformationListener) extends TypeAliases {

  /**
    * Body lookup.
    *
    * @param p_opName Name of the TLA+ operator declaration.
    * @param decls    Collection of declarations to be searched.
    * @return The body of the operator declaration, if it is an element of the collection, otherwise NullEx.
    */
  protected def findBodyOf( p_opName : String, decls : TlaDecl* ) : TlaEx = {
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
    * @param p_decls    Declarations to be considered. Must include variable declarations and all of the
    *                   non-recursive operators appearing in the spec.
    * @param p_nextName The name of the operator defining the transition relation.
    * @return A collection of symbolic transitions, if they can be extracted.
    *
    */
  def apply( p_decls : Seq[TlaDecl],
             p_nextName : String = "Next"
           ) : Seq[SymbTrans] = {

    /**
      * First, rename all bound variables to unique ones (per operator), to avoid contamination
      * when unfolding operator calls
      **/
    val declsRenamed = p_decls map {
        DeclarationModifiers.uniqueVarRename( _, m_srcDB )
      }

    val transformer = new Transformer()

    /** Make all LET-IN calls explicit, to move towards alpha-TLA+ */
    val decls = declsRenamed.map(
      {
        case TlaOperDecl( name, params, body ) =>
          TlaOperDecl( name, params, transformer.explicitLetIn( body )( m_srcDB ) )
        case e@_ => e
      }
    )

    /** Extract variable declarations */
    val vars = transformer.getVars( decls : _* )

    /** Extract transition relation */
    val nextBody = findBodyOf( p_nextName, decls : _* )

    /** If extraction failed, throw */
    //    assert( !nextBody.isNull )
    if ( nextBody == NullEx )
      throw new AssignmentException(
        "%s not found or not an operator".format( p_nextName )
      )

    /** Preprocess body (inline operators, replace UNCHANGED, turn equality to set membership, etc.) */
    val cleaned = transformer( nextBody, decls : _* )( m_bodyMap, m_srcDB )

    /** Sanity check */
    assert( cleaned.isDefined )

    val phi = cleaned.get

    val stratEncoder = new AssignmentStrategyEncoder()

    /** Generate an smt encoding of the assignment problem to pass to the SMT solver */
    val spec = stratEncoder( vars, phi )

    /** Get strategy from the solver */
    val strat = ( new SMTInterface() ) ( spec, stratEncoder.m_varSym )

    /** Throw if no strat. */
    if ( strat.isEmpty )
      throw new AssignmentException(
        "No assignment strategy found for %s".format( p_nextName )
      )

    /** From a strategy, compute symb. trans. */
    val transitions = ( new SymbTransGenerator() ) ( phi, strat.get )

    transitions

  }

}
