package at.forsyte.apalache.tla.lir

object ModuleProperty extends Enumeration {
  val Parsed, Desugared, TypeChecked, Configured, Unrolled, Inlined, Primed, VCGenerated, TransitionsFound, Preprocessed, Optimized, Analyzed = Value
}
