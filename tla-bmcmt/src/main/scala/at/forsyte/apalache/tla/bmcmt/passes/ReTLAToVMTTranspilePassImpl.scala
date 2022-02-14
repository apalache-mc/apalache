package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.assignments.ModuleAdapter
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.vmt.{Init, Next, RewriterImpl, TermWriter, Trans}
import at.forsyte.apalache.tla.lir.formulas.{Sort, StandardSorts}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.UninterpretedSort
import at.forsyte.apalache.tla.lir.{ConstT1, SetT1, StrT1, TlaConstDecl, TlaEx, TlaModule, Typed}
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog}
import at.forsyte.apalache.tla.pp.NormalizedNames
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * The reTLA to VMT transpilation pass
 *
 * @author
 *   Jure Kukovec
 */
class ReTLAToVMTTranspilePassImpl @Inject() (val options: PassOptions, pred: LanguagePred)
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
    // Disabled, for now
//    val vcActionInvs = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.VC_ACTION_INV_PREFIX)
//    val vcNotActionInvs = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.VC_NOT_ACTION_INV_PREFIX)
//    val actionInvariantsAndNegations = vcActionInvs.zip(vcNotActionInvs)
//    val vcTraceInvs = module.operDeclarations.filter(d => d.name.startsWith(NormalizedNames.VC_TRACE_INV_PREFIX))
//    val vcNotTraceInvs = module.operDeclarations.filter(d => d.name.startsWith(NormalizedNames.VC_NOT_TRACE_INV_PREFIX))
//    val traceInvariantsAndNegations = vcTraceInvs.zip(vcNotTraceInvs)
//    val optView = module.operDeclarations.find(_.name == NormalizedNames.VC_VIEW).map(_.body)

    val setConstants = module.constDeclarations
      .map { d => (d.name, d.typeTag) }
      .collect {
        case (name, Typed(SetT1(ConstT1(sortName)))) => ((name, UninterpretedSort(sortName)))
        case (name, Typed(SetT1(StrT1())))           => ((name, UninterpretedSort(StrT1().toString)))
      }
      .toMap[String, Sort]

    val rewriter = new RewriterImpl(setConstants)

    val inits = initTrans map { case (name, ex) =>
      Init(name, rewriter.rewrite(ex))
    }
    val tansitions = nextTrans map { case (name, ex) =>
      Trans(name, rewriter.rewrite(ex))
    }
    println(";Inits")
    inits.foreach(i => println(TermWriter.mkVMTString(i)))
    println(";Nexts")
    tansitions.foreach(t => println(TermWriter.mkVMTString(t)))

    Some(module)
  }

  override def dependencies = Set()
  override def transformations = Set()
}
