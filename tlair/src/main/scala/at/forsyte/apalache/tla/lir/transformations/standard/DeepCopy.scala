package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
  * DeepCopy constructs a structurally identical copy of a given TlaEx or TlaDecl, with fresh unique IDs.
  */
class DeepCopy( tracker : TransformationTracker ) {
  def deepCopyDecl[T <: TlaDecl]( decl : T ) : T = deepCopyDeclInternal( decl ).asInstanceOf[T]

  // TODO: Convert to DeclTransform once #444 is merged.
  private def deepCopyDeclInternal( decl : TlaDecl ) : TlaDecl = decl match {
    case TlaAssumeDecl( bodyEx ) => TlaAssumeDecl( deepCopyEx( bodyEx ) )
    case TlaRecFunDecl( name, arg, argDom, defBody ) =>
      TlaRecFunDecl( name, arg, deepCopyEx( argDom ), deepCopyEx( defBody ) )
    case TlaTheoremDecl(name, body) => TlaTheoremDecl(name, deepCopyEx( body ) )
    case TlaVarDecl( name ) => TlaVarDecl( name )
    case d@TlaOperDecl( name, formalParams, body) =>
      val decl = TlaOperDecl( name, formalParams, deepCopyEx( body ) )
      decl.isRecursive = d.isRecursive
      decl
    case TlaConstDecl( name ) => TlaConstDecl( name )
  }


  def deepCopyEx[T <: TlaEx]( ex : T ) : T = deepCopyExInternal( ex ).asInstanceOf[T]

  private def deepCopyExInternal : TlaExTransformation = tracker.track {
    case NullEx => NullEx
    case ValEx( v ) => ValEx( v )
    case NameEx( n ) => NameEx( n )
    case LetInEx( body, decls@_* ) =>
      LetInEx( deepCopyEx( body ), decls map deepCopyDecl : _* )
    case OperEx( oper, args@_* ) =>
      OperEx( oper, args map deepCopyEx : _* )
  }

  def deepCopyModule( module: TlaModule ) = new TlaModule( module.name, module.declarations map deepCopyDecl )

}

object DeepCopy {
  def apply( tracker : TransformationTracker ) : DeepCopy = {
    new DeepCopy( tracker )
  }
}
