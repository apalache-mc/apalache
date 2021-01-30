package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck.VarT1

class TypeVarPool(start: Int = 0) {

  /**
   * The counter that we use to produce fresh variables
   */
  private var nextVarNum = start

  def fresh: VarT1 = {
    val fresh = VarT1(nextVarNum)
    nextVarNum += 1
    fresh
  }

  def fresh(size: Int): Seq[VarT1] = {
    val vars = nextVarNum.until(nextVarNum + size).map(l => VarT1(l))
    nextVarNum += size
    vars
  }
}
