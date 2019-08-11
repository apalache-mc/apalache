package at.forsyte.apalache.tla.lir

package object transformations {
  /**
    * A general expression transformation. Although it just implements the function trait, it can be easily decorated
    * with additional behavior.
    *
    * @author Igor Konnov
    */
  type TlaExTransformation = TlaEx => TlaEx

  /**
    * A transformation that makes a module out of a module.
    */
  type TlaModuleTransformation = TlaModule => TlaModule
}
