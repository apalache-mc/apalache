package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.io.tlc.config._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
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
  private val boolOperT = OperT1(Seq(), BoolT1())

  private def mkBoolName(name: String): TlaEx = {
    tla.name(name).typed(BoolT1())
  }

  override def apply(mod: TlaModule): TlaModule = {

    val assignments = config.constAssignments.map { case (param, value) =>
      val valueEx = value.toTlaEx
      val operT = OperT1(Seq(), valueEx.typeTag.asTlaType1())
      tla.declOp(ConstAndDefRewriter.OVERRIDE_PREFIX + param, value.toTlaEx) as operT
    }
    val replacements = config.constReplacements.map { case (param, value) =>
      mod.declarations.find(_.name == value) match {
        case Some(d: TlaOperDecl) =>
          if (d.formalParams.isEmpty) {
            val tt = d.typeTag.asTlaType1()
            assert(tt.isInstanceOf[OperT1])
            val operT = tt.asInstanceOf[OperT1]
            val application = tla.appOp(tla.name(value).typed(operT)).typed(operT.res)
            tla.declOp(ConstAndDefRewriter.OVERRIDE_PREFIX + param, application) as operT
          } else {
            val nparams = d.formalParams.size
            throw new TLCConfigurationError(
                s"Met a replacement $param <- $value, where $value is an operator of $nparams parameters")
          }

        case Some(d) =>
          // This is a branch from the old untyped encoding. Does it make sense in the type encoding?
          val tt = d.typeTag.asTlaType1()
          tla.declOp(ConstAndDefRewriter.OVERRIDE_PREFIX + param, tla.name(value).typed(tt)) as OperT1(Seq(), tt)

        case None =>
          throw new TLCConfigurationError(s"Met a replacement $param <- $value, but $value is not found")
      }
    }
    val stateConstraints = config.stateConstraints.zipWithIndex.map { case (value, index) =>
      tla.declOp(TlcConfigImporter.STATE_PREFIX + index, mkBoolName(value)) as boolOperT
    }
    val actionConstraints = config.actionConstraints.zipWithIndex.map { case (value, index) =>
      tla.declOp(TlcConfigImporter.ACTION_PREFIX + index, mkBoolName(value)) as boolOperT
    }
    val invariants = config.invariants.zipWithIndex.map { case (value, index) =>
      tla.declOp(TlcConfigImporter.INVARIANT_PREFIX + index, mkBoolName(value)) as boolOperT
    }
    val temporalProps = config.temporalProps.zipWithIndex.map { case (value, index) =>
      tla.declOp(TlcConfigImporter.TEMPORAL_PREFIX + index, mkBoolName(value)) as boolOperT
    }
    val behaviorSpec = config.behaviorSpec match {
      case InitNextSpec(init, next) =>
        List(
            tla.declOp(TlcConfigImporter.INIT, mkBoolName(init)) as boolOperT,
            tla.declOp(TlcConfigImporter.NEXT, mkBoolName(next)) as boolOperT
        )

      case TemporalSpec(name) =>
        List(tla.declOp(TlcConfigImporter.SPEC, mkBoolName(name)) as boolOperT)

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
