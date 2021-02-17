package at.forsyte.apalache.tla.types

class SmtVarGenerator {
  private var idx_t: Long = 0
  private var idx_i: Long = 0

  def getFresh: SmtTypeVariable = {
    val ret = SmtTypeVariable(idx_t)
    idx_t += 1
    ret
  }

  def getNFresh(n: Int): List[SmtTypeVariable] = List.fill(n) {
    getFresh
  }

  def getFreshInt: SmtIntVariable = {
    val ret = SmtIntVariable(idx_t)
    idx_t += 1
    ret
  }

  def getNFreshInt(n: Int): List[SmtIntVariable] = List.fill(n) {
    getFreshInt
  }

}
