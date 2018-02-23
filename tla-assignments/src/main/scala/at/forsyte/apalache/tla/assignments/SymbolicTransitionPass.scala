package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.OperatorHandler

object SymbolicTransitionPass extends TypeAliases {

  protected def findBodyOf( p_opName : String, decls: TlaDecl* ) : TlaEx = {
    decls.find {
      _.name == p_opName
    }.withFilter( _.isInstanceOf[TlaOperDecl]).map( _.asInstanceOf[TlaOperDecl].body  ).getOrElse( NullEx )
  }

  def apply( p_decls : Seq[TlaDecl],
             p_nextName : String = "Next"
           ) : Seq[SymbTrans] = {

    val declsRenamed = OperatorHandler.uniqueVarRename( p_decls )

    val converter = new Converter()

    val decls = declsRenamed.map(
      decl => decl match {
        case TlaOperDecl( name, params, body ) =>
          TlaOperDecl( name, params, converter.explicitLetIn( body ) )
        case _ => decl
      }
    )

    val vars = converter.getVars( decls:_*)
    val nextBody = findBodyOf( p_nextName, decls:_* )

//    assert( !nextBody.isNull )
    if( nextBody.isNull )
      throw new AssignmentException(
        "%s not found or not an operator".format( p_nextName )
      )

    assert( nextBody.ID.valid )
//      throw new AssignmentException(
//        "%s has an invalid ID".format( p_nextName )
//      )

    val cleaned = converter( nextBody, decls : _* )

    assert( cleaned.isDefined && cleaned.get.ID.valid )
//      throw new AssignmentException(
//        "%s could not be sanitized".format( p_nextName )
//      )

    val phi = cleaned.get

    val stratEncoder = new AssignmentStrategyEncoder()

    val spec = stratEncoder( vars, phi )

    val strat = ( new SMTInterface() ) ( spec, stratEncoder.m_varSym )

    if( strat.isEmpty )
      throw new AssignmentException(
        "No assignment strategy found for %s".format( p_nextName )
      )

    val transitions = ( new SymbTransGenerator() ) ( phi, strat.get )

    transitions

  }

}
