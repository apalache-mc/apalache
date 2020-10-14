package at.forsyte.apalache.tla.assignments.passes

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.assignments.{CoverChecker, CoverData, ManualAssignments}
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class CoverAnalysisPassImpl @Inject()(options: PassOptions,
                                      tracker: TransformationTracker,
                                      @Named("AfterCoverAnalysis") nextPass: Pass with TlaModuleMixin )
  extends CoverAnalysisPass with LazyLogging {

  override def name: String = "CoverAnalysisPass"

  override def execute(): Boolean = {
    val inModule = tlaModule.get

    val operDecls = inModule.operDeclarations
    val varSet = inModule.varDeclarations.map(_.name).toSet

    val bodyMap = BodyMapFactory.makeFromDecls(operDecls)

    val initName = options.getOrElse("checker", "init", "Init")
    val initPrimedName = initName + "Primed"
    val nextName = options.getOrElse("checker", "next", "Next")

    // We check for manual assignments in InitPrime and Next
    val initBody= findBodyOf(initPrimedName, inModule.declarations: _*)
    val nextBody = findBodyOf(nextName, inModule.declarations: _*)

    val manualAssignments =
      ManualAssignments.findAll( initBody ) ++ ManualAssignments.findAll( nextBody )
    val coverChecker = new CoverChecker(varSet, manualAssignments)

    logger.info(s"  > Computing assignment cover for $nextName")
    val coverMap = bodyMap map { case (opName, TlaOperDecl( _, _, body )) =>
      // technically suboptimal, since the same CoverData is computed multiple times,
      // but no need to change it if it doesn't impact runtime
      opName -> coverChecker.coveredVars( body ).toList.sorted
    }

    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    val outFile = new File(outdir.toFile, "out-cover.txt")

    val outStr = coverMap.map {
      case (opName, coverLst) => s"${opName} covers: ${coverLst.mkString(", ")}" }
      .mkString("\n")

    val pw = new PrintWriter(new FileWriter(outFile, false))
    pw.write( outStr )
    pw.close()


    val notCovered = (varSet -- coverMap(nextName).toSet).toList.sorted
    if (notCovered.nonEmpty)
      throw new CoverData.CoverException(
        s"Operator $nextName does not cover: ${notCovered.mkString(", ")}. See ${outFile.getAbsolutePath}"
      )

    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    tlaModule map { m =>
      nextPass.setModule(m)
      nextPass
    }
  }


}