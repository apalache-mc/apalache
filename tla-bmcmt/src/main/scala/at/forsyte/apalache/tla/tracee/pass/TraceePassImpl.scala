package at.forsyte.apalache.tla.tracee.pass

import at.forsyte.apalache.infra.ExitCodes
import at.forsyte.apalache.infra.passes.DerivedPredicates
import at.forsyte.apalache.tla.tracee._
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.io.ConfigurationError
import at.forsyte.apalache.io.json.impl.DefaultTagJsonReader
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.assignments.{AssignmentOperatorIntroduction, ModuleAdapter}
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.{ModuleProperty, NullEx, TlaModule, TlaVarDecl}
import at.forsyte.apalache.tla.pp.NormalizedNames
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * The implementation of a trace evaluation encoding pass.
 *
 * @author
 *   Jure Kukovec
 */
class TraceePassImpl @Inject() (
    derivedPreds: DerivedPredicates.Configurable,
    options: OptionGroup.HasTracee,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory,
    sourceStore: SourceStore)
    extends TraceePass with LazyLogging {

  override def name: String = "TraceePass"

  // TODO: turn requires into proper error handling?
  override def execute(module: TlaModule): PassResult = {

    val traceSource = options.tracee.trace
    val traceReader = new UJsonTraceReader(Some(sourceStore), DefaultTagJsonReader)

    val trace = traceReader.convert(traceReader.read(traceSource))
    if (trace.isEmpty) {
      passFailure("The provided trace is empty.", ExitCodes.ERROR)
    } else {

      // TODO: make findBodyOf return Option? (unrelated to MVP)
      val expressions = options.tracee.expressions.map { exName =>
        findBodyOf(exName, module.operDeclarations: _*) match {
          case NullEx => throw new ConfigurationError(s"Operator $exName undefined in module ${module.name}.")
          case ex     => exName -> ex
        }
      }.toMap
      if (expressions.isEmpty)
        passFailure("The provided list of expressions is empty.", ExitCodes.ERROR)
      else {

        /*
        In this mode, we will inject our own
        Init and Nexts, but we keep CInit. Since CInit is normally
        turned into assignment-form within TransitionPass, which is skipped here,
        we must manually modify and re-insert it.
         */

        val cinitOpt =
          derivedPreds.cinit.map { cinitName =>
            val cinitEx = findBodyOf(cinitName, module.operDeclarations: _*)
            // We don't perform the standard assignment-search on cinit,
            // we just replace EVERY x' = e with x' <- e
            val tr = AssignmentOperatorIntroduction({ _ => true }, tracker)
            val newEx = tr(cinitEx)
            ModuleAdapter.exprToOperDef(NormalizedNames.CONST_INIT, newEx)
          }

        // Trace evaluation uses one variable per provided expression (for which we can reuse the name)
        val varDecls = expressions.map { case (exName, exVal) =>
          TlaVarDecl(exName)(exVal.typeTag)
        }

        // DTC constructs, for each trace state s, the transition that drives the new specification into a state,
        // where its variables hold the values the expressions would, if evaluated in state s.
        val dtc = new DrivenTransitionConstructor(tracker, expressions)

        // 1st state on the trace is init, the rest are nexts (possibly empty)
        val initEx +: nextExs = trace.map(dtc.makeTransition)

        val initOper = ModuleAdapter.exprToOperDef(NormalizedNames.INIT_PREFIX, initEx)
        val nextOpers = ModuleAdapter.exprsToOperDefs(NormalizedNames.NEXT_PREFIX, nextExs)

        // We drop certain operators in the original specification, e.g. all expression definitions, as they clash
        // with the newly-introduced variables.
        // We also don't need any of the exploration-driving operators.
        // Notably, we drop the old CInit (it's not in assignment form!), even though we use constants.
        val droppedOperNames = Set(
            derivedPreds.init,
            derivedPreds.next,
        ) ++ derivedPreds.invariants ++ derivedPreds.cinit ++ expressions.keySet

        /* TODO: Check that no operator has a dependency on the expression-defining operators. If such an operator exists, throw/abort. */

        // Drop old init/next/inv/cinit and expr defs, swap in new init/next/cinit
        // We keep the rest, since the provided expressions may have operator dependencies
        val newDecls =
          varDecls ++ module.constDeclarations ++ module.assumeDeclarations ++
            module.operDeclarations.filterNot(d =>
              droppedOperNames.contains(d.name)) ++ (initOper +: nextOpers) ++ cinitOpt

        val outModule = TlaModule(module.name, newDecls.toSeq)

        // Mark introduced transition operators as persistent, so they don't get wiped by the inlinig pass.
        derivedPreds.addPersistent(initOper.name +: nextOpers.map(_.name): _*)

        writeOut(writerFactory, outModule)

        Right(outModule)
      }
    }
  }

  override def dependencies = Set(ModuleProperty.Configured)

  override def transformations = Set()
}
