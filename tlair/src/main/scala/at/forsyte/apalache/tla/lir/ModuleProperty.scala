package at.forsyte.apalache.tla.lir

object ModuleProperty extends Enumeration {
  val TemporalEncoded, Desugared, TypeChecked, Configured, Inlined, Primed, VCGenerated, TransitionsFound, Preprocessed,
      Optimized, Analyzed = Value
}
