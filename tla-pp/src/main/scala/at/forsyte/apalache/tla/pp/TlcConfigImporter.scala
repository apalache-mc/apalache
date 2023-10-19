package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.infra.tlc.config._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.TlaModuleTransformation
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import com.typesafe.scalalogging.LazyLogging

/**
 * <p>An importer of all components of a parsed TLC config into a TLA module.</p>
 *
 * <p>Igor: This class does not compose well with the rest of ConfigurationPassImpl. So we are not using the result of
 * rewriting. We should come back to this class later.</p>
 *
 * @author
 *   Andrey Kuprianov
 */
class TlcConfigImporter(config: TlcConfig) extends TlaModuleTransformation with LazyLogging {
  private def mkBoolName(name: String): TBuilderInstruction = {
    tla.name(name, BoolT1)
  }

  override def apply(mod: TlaModule): TlaModule = {

    val assignments = config.constAssignments.map { case (param, value) =>
      val valueEx = value.toTla
      tla.decl(ConstAndDefRewriter.OVERRIDE_PREFIX + param, valueEx)
    }
    val replacements = config.constReplacements.map { case (param, value) =>
      mod.declarations.find(_.name == value) match {
        case Some(d: TlaOperDecl) =>
          if (d.formalParams.isEmpty) {
            val tt = TlaType1.fromTypeTag(d.typeTag)
            assert(tt.isInstanceOf[OperT1])
            val application = tla.appOp(tla.name(value, tt))
            tla.decl(ConstAndDefRewriter.OVERRIDE_PREFIX + param, application)
          } else {
            val nparams = d.formalParams.size
            throw new TLCConfigurationError(
                s"Met a replacement $param <- $value, where $value is an operator of $nparams parameters")
          }

        case Some(d) =>
          // This is a branch from the old untyped encoding. Does it make sense in the type encoding?
          val tt = TlaType1.fromTypeTag(d.typeTag)
          tla.decl(ConstAndDefRewriter.OVERRIDE_PREFIX + param, tla.name(value, tt))

        case None =>
          throw new TLCConfigurationError(s"Met a replacement $param <- $value, but $value is not found")
      }
    }
    val stateConstraints = config.stateConstraints.zipWithIndex.map { case (value, index) =>
      tla.decl(TlcConfigImporter.STATE_PREFIX + index, mkBoolName(value))
    }
    val actionConstraints = config.actionConstraints.zipWithIndex.map { case (value, index) =>
      tla.decl(TlcConfigImporter.ACTION_PREFIX + index, mkBoolName(value))
    }
    val invariants = config.invariants.zipWithIndex.map { case (value, index) =>
      tla.decl(TlcConfigImporter.INVARIANT_PREFIX + index, mkBoolName(value))
    }
    val temporalProps = config.temporalProps.zipWithIndex.map { case (value, index) =>
      tla.decl(TlcConfigImporter.TEMPORAL_PREFIX + index, mkBoolName(value))
    }
    val behaviorSpec = config.behaviorSpec match {
      case InitNextSpec(init, next) =>
        List(
            tla.decl(TlcConfigImporter.INIT, mkBoolName(init)),
            tla.decl(TlcConfigImporter.NEXT, mkBoolName(next)),
        )

      case TemporalSpec(name) =>
        List(tla.decl(TlcConfigImporter.SPEC, mkBoolName(name)))

      case NullSpec() =>
        throw new TLCConfigurationError("Neither INIT and NEXT, nor SPECIFICATION found in the TLC configuration file")
    }

    val extendedDecls: Iterable[TlaDecl] =
      (assignments ++ replacements ++ stateConstraints ++ actionConstraints ++ invariants ++ temporalProps ++ behaviorSpec)
        .map(_.build)
    TlaModule(mod.name, mod.declarations ++ extendedDecls)
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
