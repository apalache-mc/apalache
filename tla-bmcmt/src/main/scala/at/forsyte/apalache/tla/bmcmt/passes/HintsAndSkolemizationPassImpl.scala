package at.forsyte.apalache.tla.bmcmt.passes

import java.io.{File, PrintWriter, StringWriter}
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.assignments.ModuleManipulator
import at.forsyte.apalache.tla.bmcmt.CheckerException
import at.forsyte.apalache.tla.bmcmt.analyses.{FormulaHintsStoreImpl, FreeExistentialsStoreImpl, HintFinder, SimpleSkolemization}
import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule, TlaOperDecl}
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.{IncrementalRenaming}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * Find free-standing existential quantifiers and rename all local bindings, so they have unique names.
  *
  * TODO: clean up this mess.
  */
class HintsAndSkolemizationPassImpl @Inject()(val options: PassOptions,
                                              frexStoreImpl: FreeExistentialsStoreImpl,
                                              hintsStoreImpl: FormulaHintsStoreImpl,
                                              tracker: TransformationTracker,
                                              @Named("AfterSkolem") nextPass: Pass with TlaModuleMixin)
  extends HintsAndSkolemizationPass with LazyLogging {
  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "SkolemizationAndHints"

  object StringOrdering extends Ordering[Object] {
    override def compare(x: Object, y: Object): Int = x.toString compare y.toString
  }

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    if (tlaModule.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized")
    }
    val module = tlaModule.get
    // Rename bound variables, so each of them is unique. This is required by TrivialTypeFinder.
    // Hint by Markus Kuppe: sort init and next to get a stable ordering between the runs.
    // The most stable way is to sort them by their string representation.
    import at.forsyte.apalache.tla.assignments.ModuleManipulator.defaultNames._

    // extract the parameters
    val initTrans = ModuleManipulator.getTransitionsFromSpec( module, initDefaultName )
    val nextTrans = ModuleManipulator.getTransitionsFromSpec( module, nextDefaultName )
    val cinitP = ModuleManipulator.getOperatorOption( module, cinitDefaultName )
    val notInv = ModuleManipulator.getOperatorOption( module, notInvDefaultName )
    val notInvP = ModuleManipulator.getOperatorOption( module, notInvPrimeDefaultName )

    val oldExs = notInv ++: notInvP ++: cinitP ++: (initTrans ++ nextTrans)

    val renaming = new IncrementalRenaming(tracker)
    oldExs foreach { renaming.syncFrom }

    val initRenamed = initTrans.sorted(StringOrdering) map renaming
    val nextRenamed = nextTrans.sorted(StringOrdering) map renaming

    def renameIfDefined(ex: Option[TlaEx]): Option[TlaEx] = ex map renaming

    val constInitPrimeRenamed = renameIfDefined(cinitP)
    val notInvRenamed = renameIfDefined(notInv)
    val notInvPrimeRenamed = renameIfDefined(notInvP)

    // re-insert renamed with renamed prefix + extra renaming because NNF might introduce duplicates
    val initDecls = ModuleManipulator.declsFromTransitionBodies( s"$renamingPrefix$initDefaultName", initRenamed )
    val nextDecls = ModuleManipulator.declsFromTransitionBodies( s"$renamingPrefix$nextDefaultName", nextRenamed )
    val cinitDeclOpt = ModuleManipulator.optionalOperDecl( s"$renamingPrefix$cinitDefaultName", constInitPrimeRenamed )
    val notInvDeclOpt = ModuleManipulator.optionalOperDecl( s"$renamingPrefix$notInvDefaultName", notInvRenamed )
    val notInvPDeclOpt = ModuleManipulator.optionalOperDecl( s"$renamingPrefix$notInvPrimeDefaultName", notInvPrimeRenamed )

    // TODO: skolemization should be free of side effects. It simply finds expressions that could be skolemized.
    val skolem = new SimpleSkolemization(frexStoreImpl, tracker)

    val newDecls = cinitDeclOpt ++ notInvDeclOpt ++ notInvPDeclOpt ++ initDecls ++ nextDecls
    val normalizedDecls = renaming.normalizeDs( newDecls )
    skolem.label( normalizedDecls )

    logger.debug("Transitions after renaming and skolemization")
    for ((t, i) <- initDecls.asInstanceOf[Seq[TlaOperDecl]].zipWithIndex) {
      val stringWriter = new StringWriter()
      new PrettyWriter(new PrintWriter(stringWriter)).write(t.body)
      logger.debug("Initial transition #%d:\n%s".format(i, stringWriter.toString))
    }
    for ((t, i) <- nextDecls.asInstanceOf[Seq[TlaOperDecl]].zipWithIndex) {
      val stringWriter = new StringWriter()
      new PrettyWriter(new PrintWriter(stringWriter)).write(t.body)
      logger.debug("Next transition #%d:\n   %s".format(i, stringWriter.toString))
    }
    logger.debug("Negated invariant:\n   %s".format(notInvDeclOpt))

    val hintFinder = new HintFinder(hintsStoreImpl)
    hintFinder.findHints((initDecls ++ nextDecls).asInstanceOf[Seq[TlaOperDecl]].map(_.body))
    val newModule = new TlaModule(module.name,
      module.constDeclarations ++ module.varDeclarations ++ normalizedDecls.toSeq ++ module.assumeDeclarations)
    nextPass.setModule(newModule)

    val outdir = options.getOptionOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(newModule, new File(outdir.toFile, "out-skolem.tla"))

    val nfree = frexStoreImpl.store.size
    logger.info(s"Found $nfree free existentials in the transitions")
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    Some(nextPass)
  }
}
