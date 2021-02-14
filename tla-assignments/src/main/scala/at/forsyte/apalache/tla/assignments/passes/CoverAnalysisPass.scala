package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
 * CoverAnalysisPass reports, on a per-operator basis, which variables are covered within the body of the operator.
 */
trait CoverAnalysisPass extends Pass with TlaModuleMixin
