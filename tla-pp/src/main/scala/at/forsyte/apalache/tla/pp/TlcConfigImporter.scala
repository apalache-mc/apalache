package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.io.tlc.config._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations.{TlaModuleTransformation, TransformationTracker}
import com.typesafe.scalalogging.LazyLogging

/**
 * <p>An importer of all components of a parsed TLC config into a TLA module.</p>
 *
 * <p>Igor: This class does not compose well with the rest of ConfigurationPassImpl. So we are not using the result
 * of rewriting. We should come back to this class later.</p>
 *
 * @author Andrey Kuprianov
 */
class TlcConfigImporter(config: TlcConfig, tracker: TransformationTracker)
    extends TlaModuleTransformation with LazyLogging {
  override def apply(mod: TlaModule): TlaModule = {

    val assignments = config.constAssignments.map { case (param, value) =>
      TlaOperDecl(ConstAndDefRewriter.OVERRIDE_PREFIX + param, List(), value.toTlaEx)
    }
    val operators = Set(mod.declarations.collect { case TlaOperDecl(name, _, _) =>
      name
    }: _*)
    val replacements = config.constReplacements.map { case (param, value) =>
      if (operators.contains(value))
        TlaOperDecl(ConstAndDefRewriter.OVERRIDE_PREFIX + param, List(), OperEx(TlaOper.apply, NameEx(value)))
      else
        TlaOperDecl(ConstAndDefRewriter.OVERRIDE_PREFIX + param, List(), NameEx(value))
    }
    val stateConstraints = config.stateConstraints.zipWithIndex.map { case (value, index) =>
      TlaOperDecl(TlcConfigImporter.STATE_PREFIX + index, List(), NameEx(value))
    }
    val actionConstraints = config.actionConstraints.zipWithIndex.map { case (value, index) =>
      TlaOperDecl(TlcConfigImporter.ACTION_PREFIX + index, List(), NameEx(value))
    }
    val invariants = config.invariants.zipWithIndex.map { case (value, index) =>
      TlaOperDecl(TlcConfigImporter.INVARIANT_PREFIX + index, List(), NameEx(value))
    }
    val temporalProps = config.temporalProps.zipWithIndex.map { case (value, index) =>
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

      case NullSpec() =>
        throw new TLCConfigurationError("Neither INIT and NEXT, nor SPECIFICATION found in the TLC configuration file")
    }
    new TlaModule(mod.name,
        mod.declarations
          ++ assignments ++ replacements ++ stateConstraints ++ actionConstraints
          ++ invariants ++ temporalProps ++ behaviorSpec)
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
