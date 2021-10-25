package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.bmcmt.CheckerException
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.transformations.{TransformationTracker, fromTouchToExTransformation}
import at.forsyte.apalache.tla.lir.transformations.standard.ModuleByExTransformer
import at.forsyte.apalache.tla.lir.{NullEx, TlaAssumeDecl, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.pp.LetInOptimizer
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.io.File
import java.nio.file.Path

/**
 * Find free-standing existential quantifiers, grade expressions, and produce hints about some formulas.
 */
class AnalysisPassImpl @Inject() (val options: PassOptions, hintsStoreImpl: FormulaHintsStoreImpl,
    exprGradeStoreImpl: ExprGradeStoreImpl, tracker: TransformationTracker, writerFactory: TlaWriterFactory,
    @Named("AfterAnalysis") nextPass: Pass with TlaModuleMixin)
    extends AnalysisPass with LazyLogging {

  /**
   * The pass name.
   *
   * @return the name associated with the pass
   */
  override def name: String = "AnalysisPass"

  object StringOrdering extends Ordering[Object] {
    override def compare(x: Object, y: Object): Int = x.toString compare y.toString
  }

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    if (tlaModule.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized", NullEx)
    }

    val transformationSequence =
      List(
          // mark some expressions as to be Skolemized
          "Skolemization" -> new SkolemizationMarker(tracker),
          // mark some expressions to be expanded
          "Expansion" -> new ExpansionMarker(tracker),
          // SkolemizationMarker may introduce unused let-definitions. Remove them.
          "Remove unused let-in defs" -> fromTouchToExTransformation(new LetInOptimizer(tracker))
      ) ///

    logger.info(" > Marking skolemizable existentials and sets to be expanded...")
    val marked = transformationSequence.foldLeft(tlaModule.get) { case (m, (name, tr)) =>
      logger.info("  > %s".format(name))
      ModuleByExTransformer(tr).apply(m)
    }

    logger.info(" > Running analyzers...")

    val consts = marked.constDeclarations.map(_.name).toSet
    val vars = marked.varDeclarations.map(_.name).toSet

    val hintFinder = new HintFinder(hintsStoreImpl)
    val gradeAnalysis = new ExprGradeAnalysis(exprGradeStoreImpl)

    def analyzeExpr(expr: TlaEx): Unit = {
      gradeAnalysis.labelExpr(consts, vars, expr)
      hintFinder.introHints(expr)
    }

    marked.declarations.foreach {
      case d: TlaOperDecl   => analyzeExpr(d.body)
      case a: TlaAssumeDecl => analyzeExpr(a.body)
      case _                => ()
    }

    nextPass.setModule(marked)

    writerFactory.writeModuleAllFormats(marked.copy(name = "11_OutAnalysis"), TlaWriter.STANDARD_MODULES)

    logger.info("  > Introduced expression grades")
    logger.info("  > Introduced %d formula hints".format(hintsStoreImpl.store.size))

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
