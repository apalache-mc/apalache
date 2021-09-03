package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.VarT1

class TypeVarPool(start: Int = 0) {

  /**
   * The counter that we use to produce fresh variables
   */
  private var nextVarNum = start

  /**
   * The number of variables introduced so far, growing monotonically.
   *
   * @return the number of introduced variables
   */
  def size: Int = nextVarNum

  /**
   * Introduce a fresh type variable
   *
   * @return a new type variable that has not been used before
   */
  def fresh: VarT1 = {
    val fresh = VarT1(nextVarNum)
    nextVarNum += 1
    fresh
  }

  /**
   * Introduce a sequence of fresh type variables, that is, the variables that were not used before.
   *
   * @param size the number of variables to introduce
   * @return a sequence of fresh type variables
   */
  def fresh(size: Int): Seq[VarT1] = {
    val vars = nextVarNum.until(nextVarNum + size).map(l => VarT1(l))
    nextVarNum += size
    vars
  }
}
