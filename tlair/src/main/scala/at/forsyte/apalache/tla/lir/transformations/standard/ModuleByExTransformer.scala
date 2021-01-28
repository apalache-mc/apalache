package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TlaModuleTransformation
}

/**
  * This transformer uses a TlaExTransformer to modify all expressions inside a module.
  *
  * @author Igor Konnov
  */
class ModuleByExTransformer(exTrans: TlaExTransformation)
    extends TlaModuleTransformation {
  override def apply(mod: TlaModule): TlaModule = {
    def mapOneDeclaration: TlaDecl => TlaDecl = {
      case TlaOperDecl(name, params, body) =>
        TlaOperDecl(name, params, exTrans(body))

      case TlaAssumeDecl(body) =>
        TlaAssumeDecl(exTrans(body))

      case d => d
    }

    new TlaModule(mod.name, mod.declarations map mapOneDeclaration)
  }
}

object ModuleByExTransformer {
  def apply(exTrans: TlaExTransformation): ModuleByExTransformer =
    new ModuleByExTransformer(exTrans)
}
