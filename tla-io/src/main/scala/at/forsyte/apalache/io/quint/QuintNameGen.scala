package at.forsyte.apalache.io.quint

class QuintNameGen {
  // benign state to generate unique names for lambdas
  private var uniqueLambdaNo = 0
  // benign state to generate unique variable names
  private var uniqueVarNo = 0

  def uniqueLambdaName(): String = {
    val n = uniqueLambdaNo
    uniqueLambdaNo += 1
    s"__QUINT_LAMBDA${n}"
  }

  def uniqueVarName(): String = {
    val n = uniqueVarNo
    uniqueVarNo += 1
    s"__quint_var${n}"
  }
}
