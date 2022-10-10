package at.forsyte.apalache.tla.tracee.pass

import at.forsyte.apalache.infra.passes.DerivedPredicates
import at.forsyte.apalache.tla.tracee._
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.io.ConfigurationError
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.assignments.{AssignmentOperatorIntroduction, ModuleAdapter}
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.{IntT1, ModuleProperty, NullEx, TlaEx, TlaModule, TlaVarDecl}
import at.forsyte.apalache.tla.pp.NormalizedNames
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.types._
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * The implementation of a bounded model checker with SMT.
 *
 * @author
 *   Jure Kukovec
 */
class TraceePassImpl @Inject() (
    derivedPreds: DerivedPredicates.Configurable,
    options: OptionGroup.HasTracee,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends TraceePass with LazyLogging {

  override def name: String = "TraceePass"

  override def execute(module: TlaModule): PassResult = {
    // TODO: get trace from options
    val trace: Trace = new TraceReader().get()
    assert(trace.nonEmpty)

    // TODO: make findBodyOf return Option?
    val expressions = options.tracee.expressions.map { exName =>
      findBodyOf(exName, module.operDeclarations: _*) match {
        case NullEx => throw new ConfigurationError(s"Operator $exName undefined in module ${module.name}.")
        case ex     => exName -> ex
      }
    }.toMap
    assert(expressions.nonEmpty)

    val cinitOpt =
      derivedPreds.cinit.map { cinitName =>
        val cinitEx = findBodyOf(cinitName, module.operDeclarations: _*)
        // We don't perform the standard assignment-search on cinit,
        // we just replace EVERY x' = e with x' <- e
        val tr = AssignmentOperatorIntroduction({ _ => true }, tracker)
        val newEx = tr(cinitEx)
        ModuleAdapter.exprToOperDef(NormalizedNames.CONST_INIT, newEx)
      }

    val varDecls = expressions.map { case (exName, exVal) =>
      TlaVarDecl(exName)(exVal.typeTag)
    }

    val dtc = new DrivenTransitionConstructor(tracker, expressions)

    val initEx +: nextExs = trace.map(dtc.txToState)
    val initOper = ModuleAdapter.exprToOperDef(NormalizedNames.INIT_PREFIX, initEx)
    val nextOpers = ModuleAdapter.exprsToOperDefs(NormalizedNames.NEXT_PREFIX, nextExs)

    val droppedOperNames = Set(
        derivedPreds.init,
        derivedPreds.next,
    ) ++ derivedPreds.invariants ++ derivedPreds.cinit ++ expressions.keySet

    // Drop old init/next/inv/cinit and expr defs, swap in new init/next/cinit
    val newDecls =
      varDecls ++ module.constDeclarations ++ module.assumeDeclarations ++
        module.operDeclarations.filterNot(d => droppedOperNames.contains(d.name)) ++ (initOper +: nextOpers) ++ cinitOpt

    val outModule = TlaModule(module.name, newDecls.toSeq)

    derivedPreds.addPersistent(initOper.name +: nextOpers.map(_.name): _*)

    writeOut(writerFactory, outModule)

    Right(outModule)
  }

  override def dependencies = Set(ModuleProperty.Configured)

  override def transformations = Set()
}
