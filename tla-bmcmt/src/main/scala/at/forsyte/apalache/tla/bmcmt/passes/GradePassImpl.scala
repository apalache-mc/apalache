package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.bmcmt.CheckerException
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeAnalysis, ExprGradeStoreImpl}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * Label the specification subexpressions with grades, which are similar to TLA+ levels:
  * constant, state-level, action-level, etc. See ExprGrade.
  *
  * After the labelling is done, this pass also replaces all action-level disjunctions
  * with TlaBoolOper.orParallel.
  *
  * @author Igor Konnov
  */
class GradePassImpl @Inject()(val options: PassOptions,
                              exprGradeStoreImpl: ExprGradeStoreImpl,
                              @Named("AfterGrade") nextPass: Pass with TlaModuleMixin)
  extends GradePass with LazyLogging {

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "Grade"

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    if (tlaModule.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized")
    }

    val module = tlaModule.get
    val analysis = new ExprGradeAnalysis(exprGradeStoreImpl)
    analysis.labelWithGrades(module)

    nextPass.setModule(module)
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    Some(nextPass)
  }
}
