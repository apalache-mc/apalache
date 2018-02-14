package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.OperatorHandler
import at.forsyte.apalache.tla.assignments.Converter
import at.forsyte.apalache.tla.lir.plugins.UniqueDB

import scala.collection.immutable.Set

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

    assert( ! nextBody.isNull )

    val cleaned = converter( nextBody, decls:_* )
    assert( nextBody.ID.valid )

    assert( cleaned.isDefined )
    assert( cleaned.get.ID.valid )

    val stratEncoder = new AssignmentStrategyEncoder()

    val phi = cleaned.get

    val spec = stratEncoder( vars, phi )

    val strat = SMTInterface( spec, stratEncoder.m_varSym )

    assert( strat.isDefined )

    val transitions = SymbTransGenerator( phi, strat.get )

    transitions

  }

}
