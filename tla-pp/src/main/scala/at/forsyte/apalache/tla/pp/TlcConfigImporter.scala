package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.io.tlc.config._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaModuleTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import com.typesafe.scalalogging.LazyLogging

/**
  * An importer of all components of a parsed TLC config into a TLA module.
  *
  * @author Andrey Kuprianov
  */
class TlcConfigImporter(config: TlcConfig, tracker: TransformationTracker) extends TlaModuleTransformation with LazyLogging {
  override def apply(mod: TlaModule): TlaModule = {

    val assignments = config.constAssignments.map{
      case (param, value) =>
        TlaOperDecl(ConstAndDefRewriter.OVERRIDE_PREFIX + param, List(), ValEx(
          if(value(0).isDigit || value(0) == '-')
            TlaInt(BigInt(value))
          else
            TlaStr(value)
        ))
    }
    val replacements = config.constReplacements.map{
      case (param, value) =>
        TlaOperDecl(ConstAndDefRewriter.OVERRIDE_PREFIX + param, List(), NameEx(value))
    }
    val stateConstraints = config.stateConstraints.zipWithIndex.map{
      case (value, index) =>
        TlaOperDecl(TlcConfigImporter.STATE_PREFIX + index, List(), NameEx(value))
    }
    val actionConstraints = config.actionConstraints.zipWithIndex.map{
      case (value, index) =>
        TlaOperDecl(TlcConfigImporter.ACTION_PREFIX + index, List(), NameEx(value))
    }
    val invariants = config.invariants.zipWithIndex.map{
      case (value, index) =>
        TlaOperDecl(TlcConfigImporter.INVARIANT_PREFIX + index, List(), NameEx(value))
    }
    val temporalProps = config.temporalProps.zipWithIndex.map{
      case (value, index) =>
        TlaOperDecl(TlcConfigImporter.TEMPORAL_PREFIX + index, List(), NameEx(value))
    }
    val behaviorSpec = config.behaviorSpec match {
      case InitNextSpec(init, next) =>
        List(
          TlaOperDecl(TlcConfigImporter.INIT, List(), NameEx(init)),
          TlaOperDecl(TlcConfigImporter.NEXT, List(), NameEx(next))
        )
      case TemporalSpec(name) =>
        List(
          TlaOperDecl(TlcConfigImporter.SPEC, List(), NameEx(name))
        )
    }
    new TlaModule(mod.name, mod.declarations
      ++ assignments ++ replacements ++ stateConstraints ++ actionConstraints
      ++ invariants ++ temporalProps ++ behaviorSpec
    )
  }
}

object TlcConfigImporter {
  val STATE_PREFIX = "CONSTRAINT_$"
  val ACTION_PREFIX = "ACTION_CONSTRAINT_$"
  val INVARIANT_PREFIX = "INVARIANT_$"
  val TEMPORAL_PREFIX = "PROPERTY_$"
  val INIT = "INIT"
  val NEXT = "NEXT"
  val SPEC = "SPECIFICATION"
}
