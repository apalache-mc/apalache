package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.tla.lir.transformations.{fromTouchToExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.standard.ModuleByExTransformer
import at.forsyte.apalache.tla.lir.{TlaAssumeDecl, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.pp.LetInOptimizer
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * Find free-standing existential quantifiers, grade expressions, and produce hints about some formulas.
 */
class AnalysisPassImpl @Inject() (
    exprGradeStoreImpl: ExprGradeStoreImpl,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends AnalysisPass with LazyLogging {

  override def name: String = "AnalysisPass"

  object StringOrdering extends Ordering[Object] {
    override def compare(x: Object, y: Object): Int = x.toString.compare(y.toString)
  }

  override def execute(module: TlaModule): PassResult = {
    val transformationSequence =
      List(
          // mark some expressions as to be Skolemized
          "Skolemization" -> new SkolemizationMarker(tracker),
          // mark some expressions to be expanded
          "Expansion" -> new ExpansionMarker(tracker),
          // SkolemizationMarker may introduce unused let-definitions. Remove them.
          "Remove unused let-in defs" -> fromTouchToExTransformation(new LetInOptimizer(tracker)),
      ) ///

    logger.info(" > Marking skolemizable existentials and sets to be expanded...")
    val marked = transformationSequence.foldLeft(module) { case (m, (name, tr)) =>
      logger.info("  > %s".format(name))
      ModuleByExTransformer(tr).apply(m)
    }

    logger.info(" > Running analyzers...")

    val consts = marked.constDeclarations.map(_.name).toSet
    val vars = marked.varDeclarations.map(_.name).toSet

    val gradeAnalysis = new ExprGradeAnalysis(exprGradeStoreImpl)

    def analyzeExpr(expr: TlaEx): Unit = {
      gradeAnalysis.labelExpr(consts, vars, expr)
    }

    marked.declarations.foreach {
      case d: TlaOperDecl   => analyzeExpr(d.body)
      case a: TlaAssumeDecl => analyzeExpr(a.body)
      case _                => ()
    }

    writeOut(writerFactory, marked)

    logger.info("  > Introduced expression grades")

    Right(marked)
  }

  override def dependencies = Set(ModuleProperty.TransitionsFound)

  override def transformations = Set(ModuleProperty.Analyzed)
}
