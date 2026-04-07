package at.forsyte.apalache.tla.types

/**
 * Lightweight profiling counters for the type checker pipeline. Zero overhead when disabled (just a boolean check).
 *
 * Usage:
 * {{{
 *   TypeCheckerProfiler.enabled = true
 *   TypeCheckerProfiler.reset()
 *   // ... run type checker ...
 *   println(TypeCheckerProfiler.report())
 * }}}
 */
object TypeCheckerProfiler {
  // Auto-enable via -Dapalache.typechecker.profile=true
  @volatile var enabled: Boolean =
    sys.props.getOrElse("apalache.typechecker.profile", "false").equalsIgnoreCase("true")

  // TypeUnifier.unify() counters
  var unifyCallCount: Long = 0
  var unifyTotalNanos: Long = 0
  var unifyMaxNanos: Long = 0

  // Substitution.subRec() counters
  var subRecCallCount: Long = 0
  var subRecTotalIterations: Long = 0
  var subRecMaxIterations: Long = 0

  // ConstraintSolver.solvePartially() counters
  var solvePartiallyCallCount: Long = 0
  var solvePartiallyTotalLoopIterations: Long = 0

  // ConstraintSolver.isFreeVar() counters
  var isFreeVarCallCount: Long = 0

  def reset(): Unit = {
    unifyCallCount = 0
    unifyTotalNanos = 0
    unifyMaxNanos = 0
    subRecCallCount = 0
    subRecTotalIterations = 0
    subRecMaxIterations = 0
    solvePartiallyCallCount = 0
    solvePartiallyTotalLoopIterations = 0
    isFreeVarCallCount = 0
  }

  def report(): String = {
    val sb = new StringBuilder
    sb.append("=== Type Checker Profile ===\n")
    sb.append(f"TypeUnifier.unify():  calls=$unifyCallCount, totalMs=${unifyTotalNanos / 1e6}%.1f, maxMs=${unifyMaxNanos / 1e6}%.3f\n")
    sb.append(f"Substitution.subRec(): calls=$subRecCallCount, totalIters=$subRecTotalIterations, maxIters=$subRecMaxIterations\n")
    sb.append(f"ConstraintSolver.solvePartially(): calls=$solvePartiallyCallCount, totalLoopIters=$solvePartiallyTotalLoopIterations\n")
    sb.append(f"isFreeVar(): calls=$isFreeVarCallCount\n")
    if (subRecCallCount > 0) {
      sb.append(f"  avg subRec iterations: ${subRecTotalIterations.toDouble / subRecCallCount}%.2f\n")
    }
    if (unifyCallCount > 0) {
      sb.append(f"  avg unify time: ${unifyTotalNanos.toDouble / unifyCallCount / 1e6}%.3f ms\n")
    }
    sb.append("============================\n")
    sb.toString()
  }
}
