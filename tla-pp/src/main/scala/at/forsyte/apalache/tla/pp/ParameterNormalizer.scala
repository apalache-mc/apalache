package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TlaModuleTransformation,
  TransformationTracker
}

/**
  * Transforms a declaration A(x,y(_,_)) == e
  * into parameter-normal form, i.e.
  * A(x,y(_,_)) == LET x_new == x
  *               y_new(p1, p2) == y(p1,p2)
  *           IN e[ x_new/x, y_new/y ]
  * This allows us to limit the number of substitutions when inlining A.
  * @param decisionFn Normal-form transformation will only be applied to operator declarations (both top-level and LET-IN),
  *                   for which `decisionFn` evaluates to true. Default: returns true for all recursive operators.
  */
class ParameterNormalizer(
    nameGenerator: UniqueNameGenerator,
    tracker: TransformationTracker,
    decisionFn: TlaOperDecl => Boolean
) {

  /** Declaration-level transformation */
  def normalizeDeclaration(decl: TlaOperDecl): TlaOperDecl = {
    // Since the body may contain LET-IN defined operators, we first normalize all of them
    val normalizedBody = normalizeInternalLetIn(decl.body)
    val newBody =
      if (decisionFn(decl))
        normalizeParametersInEx(decl.formalParams)(normalizedBody)
      else normalizedBody
    val newDecl = decl.copy(body = newBody)
    // Copy doesn't preserve .isRecursive!
    newDecl.isRecursive = decl.isRecursive
    newDecl
  }

  /** Expression-level LET-IN transformation, applies `mkParamNormalForm` to all LET-IN declarations */
  private def normalizeInternalLetIn: TlaExTransformation = tracker.track {
    case ex @ LetInEx(body, defs @ _*) =>
      val newDefs = defs map { d =>
        normalizeDeclaration(d)
      }
      val newBody = normalizeInternalLetIn(body)
      if (defs == newDefs && body == newBody) ex
      else LetInEx(newBody, newDefs: _*)

    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map normalizeInternalLetIn
      if (args == newArgs) ex
      else OperEx(op, newArgs: _*)

    case ex => ex

  }

  /** Iteratively introduces a new operator for each formal parameter */
  private def normalizeParametersInEx(
      paramNames: List[FormalParam]
  ): TlaExTransformation = tracker.track { ex =>
    paramNames.foldLeft(ex) {
      case (partialEx, fParam) =>
        val paramOperName = nameGenerator.newName()
        fParam match {
          case SimpleFormalParam(name) =>
            // We replace all instances of `fParam` with `paramOperName`
            // however, since paramOperName is an operator, we have to replace with application
            val tr = ReplaceFixed(
              NameEx(fParam.name),
              OperEx(TlaOper.apply, NameEx(paramOperName)),
              tracker
            )
            val replaced = tr(partialEx)
            // if fParam is simple, the introduced operator is nullary
            val letInDef = TlaOperDecl(paramOperName, List.empty, NameEx(name))
            LetInEx(replaced, letInDef)

          case OperFormalParam(name, arity) =>
            // We again replace all instances of `fParam` with `paramOperName`
            // As both are operators, we don't need to introduce application
            val tr = ReplaceFixed(
              NameEx(fParam.name),
              NameEx(paramOperName),
              tracker
            )
            val replaced = tr(partialEx)

            // This time, the introduced operator is not nullary, so we need to invent parameters
            val inventedParams = List.fill(arity) {
              nameGenerator.newName()
            }
            // The body is just the operator applied to all the parameters
            val newBody = OperEx(
              TlaOper.apply,
              name +: inventedParams map NameEx: _*
            )
            val letInDef = TlaOperDecl(
              paramOperName,
              inventedParams map SimpleFormalParam,
              newBody
            )
            LetInEx(replaced, letInDef)
        }
    }
  }

  /** Module-level transformation, calls `mkParamNormalForm` on all operator declarations */
  def normalizeModule: TlaModuleTransformation = { m =>
    val newDecls = m.declarations map {
      case d: TlaOperDecl => normalizeDeclaration(d)
      case d              => d
    }
    new TlaModule(m.name, newDecls)

  }

}

object ParameterNormalizer {

  // Two standard options for `decisionFn`
  object DecisionFn {
    def all: TlaOperDecl => Boolean = _ => true
    def recursive: TlaOperDecl => Boolean = _.isRecursive
  }

  def apply(
      nameGenerator: UniqueNameGenerator,
      tracker: TransformationTracker,
      decisionFn: TlaOperDecl => Boolean = DecisionFn.recursive
  ): ParameterNormalizer =
    new ParameterNormalizer(nameGenerator, tracker, decisionFn)
}
