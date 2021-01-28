package at.forsyte.apalache.tla.lir

package object transformations {
  /**
    * A general expression transformation.
    */
  type TlaExTransformation = TlaEx => TlaEx

  /**
    * A transformation that makes a module out of a module.
    */
  type TlaModuleTransformation = TlaModule => TlaModule
}
