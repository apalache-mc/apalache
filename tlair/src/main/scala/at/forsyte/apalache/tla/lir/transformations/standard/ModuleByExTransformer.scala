package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation}

/**
 * This transformer uses a TlaExTransformer to modify the bodies of operator declarations inside a module.
 *
 * @author Igor Konnov
 */
class ModuleByExTransformer(
    exTrans: TlaExTransformation, applyTo: (TlaDecl => Boolean) = (_ => true)
) extends TlaModuleTransformation {
  override def apply(mod: TlaModule): TlaModule = {
    def mapOneDeclaration: TlaDecl => TlaDecl = {
      case d @ TlaOperDecl(_, _, body) =>
        val newBody = exTrans(body)
        if (newBody.ID == d.body.ID) {
          d
        } else {
          d.copy(body = newBody)
        }

      case d @ TlaAssumeDecl(body) =>
        val newBody = exTrans(body)
        if (newBody.ID == body.ID) {
          d
        } else {
          TlaAssumeDecl(newBody)(d.typeTag)
        }

      case d => d
    }

    def mapIfIncluded(decl: TlaDecl): TlaDecl = {
      if (applyTo(decl)) {
        mapOneDeclaration(decl)
      } else {
        decl
      }
    }

    new TlaModule(mod.name, mod.declarations map mapIfIncluded)
  }
}

object ModuleByExTransformer {
  def apply(exTrans: TlaExTransformation): ModuleByExTransformer =
    new ModuleByExTransformer(exTrans)

  def apply(
      exTrans: TlaExTransformation, include: TlaDecl => Boolean
  ): ModuleByExTransformer =
    new ModuleByExTransformer(exTrans, include)
}
