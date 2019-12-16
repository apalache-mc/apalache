package at.forsyte.apalache.tla.types.smt

abstract class IndexEvaluator {
  def getValue( i: Int ) : Int
}