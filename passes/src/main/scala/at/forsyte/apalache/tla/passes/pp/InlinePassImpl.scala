package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations._
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp._
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.DerivedPredicates

/**
 * A pass that expands operators and let-in definitions, as well as primitive-valued CONSTANTs.
 */
class InlinePassImpl @Inject() (
    derivedPreds: DerivedPredicates,
    tracker: TransformationTracker,
    renaming: IncrementalRenaming,
    writerFactory: TlaWriterFactory)
    extends InlinePass with LazyLogging {

  override def name: String = "InlinePass"

  override def execute(module: TlaModule): PassResult = {
    // Since PrimingPass now happens before inlining, we have to add InitPrime and CInitPrime as well
    val initName = derivedPreds.init
    val cinitName = derivedPreds.cinit.getOrElse("CInit") // TODO: why default on None here?
    val initPrimedName = initName + "Primed"
    val cinitPrimedName = cinitName + "Primed"

    // Fixing issue 283: https://github.com/informalsystems/apalache/issues/283
    // Remove the operators that are not needed,
    // as some of them may contain higher-order operators that cannot be substituted
    val relevantOperators = derivedPreds.operatorNames().toSet
    val relevantOperatorsAndInitCInitPrimed = relevantOperators + initPrimedName + cinitPrimedName

    logger.info("Leaving only relevant operators: " + relevantOperatorsAndInitCInitPrimed.toList.sorted.mkString(", "))
    val moduleFilter = Inliner.FilterFun.RESTRICT_TO(relevantOperatorsAndInitCInitPrimed)

    // We have to rename the input, as LOCAL-toplevel TLA+ functions get
    // introduced as LET-IN operators (copying the definition). The problem is,
    // the operator bodies may introduce namespace collisions, e.g. with
    //
    // LOCAL f[x \in S] = x
    // Op(x) == f[x + 1]
    //   |
    //   V
    // Op(x) == LET f == [x \in S] In f[(x + 1)] <- namespace collision on x
    //
    val renamedModule = renaming.renameInModule(module)

    val inliner = new Inliner(tracker, renaming, keepNullaryMono = true, moduleLevelFilter = moduleFilter)
    val inlined = inliner.transformModule(renamedModule)

    // Inline the primitive constants now
    val constants = module.constDeclarations.map { _.name }
    val cInitBody = findBodyOf(cinitName, inlined.declarations: _*)
    val constInliner = TlaConstInliner(tracker, constants.toSet)
    val constMap = constInliner.buildConstMap(Map.empty)(cInitBody)
    val declTr: TlaDeclTransformation = tracker.trackDecl {
      // When inlining, we keep the original CInit(Primed)
      case d @ TlaOperDecl(name, _, body) if (name != cinitName && name != cinitPrimedName) =>
        d.copy(body = constInliner.replaceConstWithValue(constMap)(body))(d.typeTag)
      case d => d // keep the rest as they are
    }
    val constInlinedModule = inlined.copy(
        declarations = inlined.declarations.map(declTr)
    )

    // dump the result of preprocessing
    writeOut(writerFactory, constInlinedModule)

    Right(constInlinedModule)
  }

  override def dependencies = Set()

  override def transformations = Set(ModuleProperty.Inlined)
}
