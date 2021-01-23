package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TlaModuleTransformation
}

/**
  * This transformer uses a TlaExTransformer to modify expressions inside a module.
  *
  * @author Igor Konnov
  */
class ModuleByExTransformer(
    exTrans: TlaExTransformation,
    applyTo: (TlaDecl => Boolean) = (_ => true)
) extends TlaModuleTransformation {
  override def apply(mod: TlaModule): TlaModule = {
    def mapOneDeclaration: TlaDecl => TlaDecl = {
      case TlaOperDecl(name, params, body) =>
        TlaOperDecl(name, params, exTrans(body))

      case TlaAssumeDecl(body) =>
        TlaAssumeDecl(exTrans(body))

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
      exTrans: TlaExTransformation,
      include: TlaDecl => Boolean
  ): ModuleByExTransformer =
    new ModuleByExTransformer(exTrans, include)
}
