package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}
import TypedPredefs._

/**
 * Transforms a declaration A(x,y(_,_)) == e
 * into parameter-normal form, i.e.
 * A(x,y(_,_)) == LET x_new == x
 * y_new(p1, p2) == y(p1,p2)
 * IN e[ x_new/x, y_new/y ]
 * This allows us to limit the number of substitutions when inlining A.
 *
 * @param decisionFn Normal-form transformation will only be applied to operator declarations (both top-level and LET-IN),
 *                   for which `decisionFn` evaluates to true. Default: returns true for all recursive operators.
 */
class ParameterNormalizer(
    nameGenerator: UniqueNameGenerator, tracker: TransformationTracker, decisionFn: TlaOperDecl => Boolean
) {

  /** Declaration-level transformation */
  def normalizeDeclaration(decl: TlaOperDecl): TlaOperDecl = {
    // Since the body may contain LET-IN defined operators, we first normalize all of them
    val normalizedBody = normalizeInternalLetIn(decl.body)
    val paramTypes = extractParamTypes(decl)
    val newBody =
      if (decisionFn(decl)) normalizeParametersInEx(decl.formalParams, paramTypes)(normalizedBody)
      else normalizedBody
    val newDecl = decl.copy(body = newBody)
    // Copy doesn't preserve .isRecursive!
    newDecl.isRecursive = decl.isRecursive
    newDecl
  }

  // extract parameter types from the type tag
  private def extractParamTypes(decl: TlaOperDecl): Seq[TlaType1] = {
    decl.typeTag match {
      case Typed(OperT1(paramTypes, _)) =>
        val typeParamCount = paramTypes.length
        val sigParamCount = decl.formalParams.length
        if (typeParamCount == sigParamCount) {
          paramTypes
        } else {
          throw new TypingException(
              "The signature of operator %s has %d parameters whereas the type tag has %d parameters"
                .format(decl.name, sigParamCount, typeParamCount))
        }

      case _ =>
        throw new TypingException(s"Operator ${decl.name} has an invalid type tag: " + decl.typeTag)
    }
  }

  /** Expression-level LET-IN transformation, applies `mkParamNormalForm` to all LET-IN declarations */
  private def normalizeInternalLetIn: TlaExTransformation = tracker.trackEx {
    case ex @ LetInEx(body, defs @ _*) =>
      val newDefs = defs map { d => normalizeDeclaration(d) }
      val newBody = normalizeInternalLetIn(body)
      if (defs == newDefs && body == newBody) ex
      else LetInEx(newBody, newDefs: _*)(ex.typeTag)

    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map normalizeInternalLetIn
      if (args == newArgs) ex
      else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex => ex

  }

  /** Iteratively introduces a new operator for each formal parameter */
  private def normalizeParametersInEx(paramNames: Seq[FormalParam], paramTypes: Seq[TlaType1]): TlaExTransformation =
    tracker.trackEx { ex =>
      paramNames.zip(paramTypes).foldLeft(ex) { case (partialEx, (fParam, fParamType)) =>
        val paramOperName = nameGenerator.newName()
        (fParam, fParamType) match {
          case (SimpleFormalParam(name), paramType) =>
            // case 1: a normal parameter, not a higher-order one.
            // We replace all instances of `fParam` with `paramOperName()`
            // however, since paramOperName is an operator, we have to replace with application
            val types = Map("t" -> OperT1(Seq(), paramType), "p" -> fParamType)
            val tr = ReplaceFixed(tracker)(
                tla.name(fParam.name).typed(types, "p"),
                tla.appOp(tla.name(paramOperName) ? "t").typed(types, "p")
            )
            val replaced = tr(partialEx)
            // if fParam is simple, the introduced operator is nullary
            val letInDef =
              tla
                .declOp(paramOperName, tla.name(name).typed(types, "p"))
                .typedOperDecl(types, "t")
            tla
              .letIn(replaced, letInDef)
              .typed(types, "p")

          case (OperFormalParam(name, arity), paramType) =>
            // case 2: a higher-order parameter.
            // We again replace all instances of `fParam` with `paramOperName`
            // As both are operators, we don't need to introduce application
            val tr = ReplaceFixed(tracker)(
                tla.name(fParam.name).typed(paramType),
                tla.name(paramOperName).typed(paramType)
            )
            val replaced = tr(partialEx)

            // This time, the introduced operator is not nullary, so we need to introduce fresh parameters
            val freshParams = List.fill(arity) {
              nameGenerator.newName()
            }

            paramType match {
              case OperT1(hoParamTypes, resType) =>
                // The body is just the operator applied to the fresh parameters
                val freshParamsWithTypes = freshParams.zip(hoParamTypes).map { case (n, t) => tla.name(n).typed(t) }
                val newBody =
                  tla
                    .appOp(
                        tla.name(name).typed(paramType),
                        freshParamsWithTypes: _*
                    )
                    .typed(resType)
                val letInDef = tla
                  .declOp(paramOperName, newBody, freshParams map SimpleFormalParam: _*)
                  .typedOperDecl(paramType)
                tla.letIn(replaced, letInDef).typed(resType)

              case _ =>
                throw new TypingException(s"Expected a higher-order parameter $name, found type: $paramType")
            }
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
      nameGenerator: UniqueNameGenerator, tracker: TransformationTracker,
      decisionFn: TlaOperDecl => Boolean = DecisionFn.recursive
  ): ParameterNormalizer =
    new ParameterNormalizer(nameGenerator, tracker, decisionFn)
}
