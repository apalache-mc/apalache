package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}

class ParameterNormalizer(
                           nameGenerator: UniqueNameGenerator,
                           tracker: TransformationTracker,
                           decisionFn: TlaOperDecl => Boolean
                         ) {

  // Transforms a declaration A(x,y(_,_)) == e
  // into A(x,y) == LET x_new == x
  //                    y_new( p1, p2) == y(p_1,p_2)
  //                IN e[ x_new/x, y_new/y ]
  // This allows us to limit the number of substitutions when inlining A
  def mkParamNormalForm( decl : TlaDecl ) : TlaDecl = decl match {
    case d@TlaOperDecl( name, params, body ) =>
      val newDecl = d.copy( body = paramNormal( params )( body ) )
      // Copy doesn't preserve .isRecursive!
      newDecl.isRecursive = d.isRecursive
      newDecl
    case _ => decl
  }

  private def paramNormal( paramNames : List[FormalParam] ) : TlaExTransformation = tracker.track { ex =>
    paramNames.foldLeft( ex ) {
      case (partialEx, fParam) =>
        // For each formal parameter we invent a fresh operator name
        val paramOperName = nameGenerator.newName()
        // We split now, based on whether fParam is a simple or operator parameter
        fParam match {
          case SimpleFormalParam( name ) =>
            // We replace all instances of `fParam` with `paramOperName`
            // however, since paramOperName is an operator, we have to replace with application
            val tr = ReplaceFixed(
              NameEx( fParam.name ),
              OperEx( TlaOper.apply, NameEx( paramOperName ) ),
              tracker
            )
            val replaced = tr( partialEx )
            // if fParam is simple, the introduced operator is nullary
            val letInDef = TlaOperDecl( paramOperName, List.empty, NameEx( name ) )
            LetInEx( replaced, letInDef )

          case OperFormalParam( name, arity ) =>
            // We again replace all instances of `fParam` with `paramOperName`
            // As both are operators, we don't need to introduce application
            val tr = ReplaceFixed(
              NameEx( fParam.name ),
              NameEx( paramOperName ),
              tracker
            )
            val replaced = tr( partialEx )

            // This time, the introduced operator is not nullary, so we need to invent parameters
            val inventedParams = List.fill( arity ) {
              nameGenerator.newName()
            }
            // The body is just the operator applied to all the parameters
            val newBody = OperEx(
              TlaOper.apply, name +: inventedParams map NameEx : _*
            )
            val letInDef = TlaOperDecl( paramOperName, inventedParams map SimpleFormalParam, newBody )
            LetInEx( replaced, letInDef )
        }
    }
  }

  def normalize : TlaModuleTransformation = { m =>
    // Iterates over all declarations and replaces those for which decisionFn returns true
    // (by default, for all recursive)
    val newDecls = m.declarations map {
      case d : TlaOperDecl if decisionFn( d ) =>
        mkParamNormalForm( d )
      case d => d
    }
    new TlaModule( m.name, newDecls )

  }

}

object ParameterNormalizer {

  object DecisionFn {
    def all : TlaOperDecl => Boolean = _ => true
    def recursive : TlaOperDecl => Boolean = _.isRecursive
  }

  def apply(
             nameGenerator : UniqueNameGenerator,
             tracker : TransformationTracker,
             decisionFn : TlaOperDecl => Boolean = DecisionFn.recursive
           ) : ParameterNormalizer =
    new ParameterNormalizer( nameGenerator, tracker, decisionFn )
}