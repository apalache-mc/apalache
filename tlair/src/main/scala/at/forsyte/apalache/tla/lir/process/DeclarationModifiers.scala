package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations.{TransformationListener, VariableRenamingTracker}

object DeclarationModifiers {
  /**
    * Temporarily moved here from OperatorHandler while we figure out how to structure Renaming
    *
    * TODO: shall we move this class to *.lir.transformations.standard
    */
  def uniqueVarRename( decl : TlaDecl, listeners : TransformationListener* ) : TlaDecl =
    decl match {
      case TlaOperDecl( name, params, body ) =>
        TlaOperDecl(
          name,
          params.map( VariableRenamingTracker.renameParam( prefix = name ) ),
          VariableRenamingTracker( listeners : _* ).VariableRenaming(
            params.map( _.name ).toSet,
            name
          )( body )
        )
      case _ => decl
    }
}
