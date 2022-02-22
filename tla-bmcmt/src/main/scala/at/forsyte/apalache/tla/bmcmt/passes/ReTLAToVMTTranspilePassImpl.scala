package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.assignments.ModuleAdapter
import at.forsyte.apalache.tla.bmcmt.rules.vmt.VMTWriter
import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog}
import at.forsyte.apalache.tla.pp.{NormalizedNames, UniqueNameGenerator}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * The reTLA to VMT transpilation pass
 *
 * @author
 *   Jure Kukovec
 */
class ReTLAToVMTTranspilePassImpl @Inject() (val options: PassOptions, pred: LanguagePred, gen: UniqueNameGenerator)
    extends TranspilePass with LazyLogging {

  override def name: String = "Transpiler"

  private def getTransitionsWithNames(module: TlaModule, prefix: String): Seq[(String, TlaEx)] =
    module.operDeclarations
      .filter {
        _.name.startsWith(prefix) // transitions end in 0,1,...
      }
      .sortBy(_.name)
      .map { d =>
        (d.name, d.body)
      }

  override def execute(module: TlaModule): Option[TlaModule] = {
    // Check if still ok fragment (sanity check, see postTypeChecker)
    LanguageWatchdog(pred).check(module)

    val initTrans = getTransitionsWithNames(module, NormalizedNames.INIT_PREFIX)
    val nextTrans = getTransitionsWithNames(module, NormalizedNames.NEXT_PREFIX)
    val cinitP = getTransitionsWithNames(module, NormalizedNames.CONST_INIT)
    val vcInvs = getTransitionsWithNames(module, NormalizedNames.VC_INV_PREFIX)
    val vcActionInvs = getTransitionsWithNames(module, NormalizedNames.VC_ACTION_INV_PREFIX)

    val vmtWriter = new VMTWriter(gen)

    vmtWriter.annotateAndWrite(module.varDeclarations, module.constDeclarations, cinitP, initTrans, nextTrans,
        vcInvs ++ vcActionInvs)

    Some(module)
  }

  override def dependencies = Set()
  override def transformations = Set()
}
