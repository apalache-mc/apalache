package at.forsyte.apalache.tla.assignments.passes

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.assignments.{CoverChecker, ManualAssignments}
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.lir.src.SourceLocation
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class CoverAnalysisPassImpl @Inject()(options: PassOptions,
                                      sourceStore: SourceStore,
                                      changeListener: ChangeListener,
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
    val mustCoverMap = bodyMap map { case (opName, TlaOperDecl( _, _, body )) =>
      // technically suboptimal, since the same CoverData is computed multiple times,
      // but no need to change it if it doesn't impact runtime
      opName -> coverChecker.coveredVars( body )
    }
    // we compute assignment witnesses
    val asgns =
      coverChecker.assignmentLocaitons( nextBody ) ++ coverChecker.assignmentLocaitons( initBody )

    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    val outFile = new File(outdir.toFile, "out-cover.txt")

    val sourceLoc = SourceLocator(sourceStore.makeSourceMap, changeListener)

    // we add source info
    val locVarSet = asgns map {
      cand =>
        ( cand.varName, sourceLoc.sourceOf( cand.uid ) )
      } // duplicates are removed

    // We remove all assignments for which source info isn't available
    // and sort the rest by source
    val sortedAsgns =
      locVarSet.toList.withFilter {
        _._2.nonEmpty
      } map { case (x, yOpt) =>
        (x, yOpt.get)
      } sortBy {
        _._2
      }

    // For each operator, we compute the SourceLocation of its body
    val opLocs = bodyMap map {
      case (opName, opDecl) => opName -> sourceLoc.sourceOf( bodyMap(opName).body.ID )
    }

    // Given a SourceLocation, we can find the operator containing it, if it exists
    def definingOper( loc: SourceLocation ) : Option[String] =
      bodyMap.keySet.find {
        opName =>
          opLocs(opName).exists {
            bodyLoc : SourceLocation =>
              bodyLoc.region.contains( loc.region )
          }
      }

    val defaultOpName = "<UNKNOWN>"

    // We prepare the triplets that will be passed to the format strings
    val outTriples = sortedAsgns map { case (varName, loc) =>
      ( loc.toString, definingOper( loc ).getOrElse(defaultOpName), varName )
    }

    // From them, we generate a may-cover map, by aggregating the variables for each operator
    val mayCoverMap: Map[String, Set[String]] =
      outTriples.foldLeft( Map.empty[String,Set[String]] ) {
        case (m, (_, opName, varName)) =>
          m + ( opName -> ( m.getOrElse( opName, Set.empty ) + varName ) )
      }

    // For nicer formatting, we compute the max width for the source and name fields
    val longestLoc = outTriples.map( _._1.length ).max
    val longestOpName = outTriples.map( _._2.length ).max

    val formatStringMay = s"%-${longestLoc}s: %${longestOpName}s may update %s"
    val formatStringMust = s"%-${longestLoc}s: %${longestOpName}s always updates: %s"
    val formatStringWarning = s"%-${longestLoc}s: %${longestOpName}s sometimes does not update: %s \t [WARNING!] "

    // The first part of the output lists all assignment witnesses
    val outStrMay = outTriples.map { case (loc, opName, varName) =>
      formatStringMay.format( loc, opName, varName )
    }.mkString("\n") ++ "\n\n"

    def sortedVarString( s: Set[String] ) = s.toList.sorted.mkString(", ")

    // The second part of the output lists, for each operator, all variables it must update (if any)
    // and a warning for each variable that may be updated but is not guaranteed to be updated
    val outStrMustWarning = mayCoverMap.keySet.toList.sortBy( k => opLocs(k).get) flatMap { opName: String =>
      val locOpt = opLocs(opName)
      locOpt map { loc =>
        // for Init we know any updates appear only in InitPrime
        val initPrimeNameCorrection = if (opName == initName) initPrimedName else opName
        val mustVars = mustCoverMap.getOrElse( initPrimeNameCorrection, Set.empty )
        // if there are no guaranteed vars we don't want any output
        val mustStrOpt =
          if (mustVars.isEmpty)
            None
          else
            Some( formatStringMust.format( loc.toString, opName, sortedVarString(mustVars) ) )
        val notGuaranteed = mayCoverMap(opName) -- mustVars
        // Similarly, we only want to see a warning if `notGuaranteed` is nonempty
        val warningOpt =
          if (notGuaranteed.isEmpty)
            None
          else
            Some( formatStringWarning.format( loc.toString, opName, sortedVarString( notGuaranteed)  ) )

        List( mustStrOpt, warningOpt ).flatten.mkString("\n")
      }
    } mkString "\n"

    val outStr = outStrMay + outStrMustWarning

    val pw = new PrintWriter(new FileWriter(outFile, false))
    pw.write( outStr )
    pw.close()

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