package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import scalaz.unused

/**
 * TlaExToVMTWriter handles the last step of transpiling: assembling the .vmt output file.
 *
 * Given a disassembled module (extracted init, next, inv, etc.) VMTWriter determines which parts get which `VMTExpr`
 * wrappers. Then, using TermToVMTWriter, it translates the VMT terms to output strings, and adds sort/function
 * declarations and definitions.
 *
 * @author
 *   Jure Kukovec
 */
class TlaExToVMTWriter(gen: UniqueNameGenerator) {
  // Main entry point.
  def annotateAndWrite(
      varDecls: Seq[TlaVarDecl],
      constDecls: Seq[TlaConstDecl],
      @unused cInit: Seq[(String, TlaEx)],
      initTransitions: Seq[(String, TlaEx)],
      nextTransitions: Seq[(String, TlaEx)],
      invariants: Seq[(String, TlaEx)]): Unit = {

    // First, we parse the constant declarations, to extract all restricted sets, i.e.,
    // constants typed with SetT1(ConsT1(_))
    val setConstants = constDecls
      .map { d => (d.name, d.typeTag) }
      .collect {
        case (name, Typed(SetT1(ConstT1(sortName)))) => (name, UninterpretedSort(sortName))
        case (name, Typed(SetT1(StrT1)))             => (name, UninterpretedSort(StrT1.toString))
      }
      .toMap[String, UninterpretedSort]

    val rewriter = new ToTermRewriterImpl(setConstants, gen)

    // Not sure what to do with CInits yet, we might want to add them ass axioms later
//    val cinits = cInit.map { case (_, ex) =>
//      rewriter.rewrite(ex)
//    }
//    val cinitStrs = cinits.map(TermToVMTWriter.mkSMT2String)

    // convenience shorthand
    def rewrite: TlaEx => TermBuilderT = rewriter.rewrite

    // Each transition in initTransitions needs the VMT wrapper Init
    val initCmps = cmpSeq(initTransitions.map { case (name, ex) =>
      rewrite(ex).map { Init(name, _) }
    })

    // Each transition in nextTransitions needs the VMT wrapper Trans
    val transitionCmps = cmpSeq(nextTransitions.map { case (name, ex) =>
      rewrite(ex).map { Trans(name, _) }
    })

    // Each invariant in invariants needs the VMT wrapper Invar
    val invCmps = cmpSeq(invariants.zipWithIndex.map { case ((name, ex), i) =>
      rewrite(ex).map { Invar(name, i, _) }
    })

    val (smtDecls, (inits, transitions, invs)) = (for {
      initTerms <- initCmps
      transitionTerms <- transitionCmps
      invTerms <- invCmps
    } yield (initTerms, transitionTerms, invTerms)).run(SmtDeclarations.init)

    val initStrs = inits.map(TermToVMTWriter.mkVMTString)

    val transStrs = transitions.map(TermToVMTWriter.mkVMTString)

    val invStrs = invs.map(TermToVMTWriter.mkVMTString)

    // Each variable v in varDecls needs the VMT binding Next(v, v')
    val nextBindings = varDecls.map { case d @ TlaVarDecl(name) =>
      val sort = TlaType1ToSortConverter.sortFromType(d.typeTag.asTlaType1())
      Next(nextName(name), mkVariable(name, sort), mkVariable(VMTprimeName(name), sort))
    }

    val nextStrs = nextBindings.map(TermToVMTWriter.mkVMTString)

    // Variable declarations
    val smtVarDecls = varDecls.map(TermToVMTWriter.mkSMTDecl)

    // Sort declaration
    val allSorts = setConstants.values.toSet ++ smtDecls.uninterpretedSorts.map(UninterpretedSort)
    val sortDecls = allSorts.map(TermToVMTWriter.mkSortDecl)

    // Uninterpreted literal declaration and uniqueness assert
    val ulitDecls = smtDecls.uninterpretedLiterals.values.map(TermToVMTWriter.mkConstDecl)
    val disticntAsserts = allSorts.flatMap { s =>
      val litsForSortS = smtDecls.uninterpretedLiterals.values.filter {
        _.sort == s
      }
      (if (litsForSortS.size > 1) Some(litsForSortS) else None).map(TermToVMTWriter.assertDistinct)
    }

    OutputManager.withWriterInRunDir(TlaExToVMTWriter.outFileName) { writer =>
      writer.println(";Sorts")
      sortDecls.foreach(writer.println)
      writer.println()
      writer.println(";Constants")
      ulitDecls.foreach(writer.println)
      writer.println()
      disticntAsserts.foreach(writer.println)
      writer.println()
      writer.println(";Variables")
      smtVarDecls.foreach(writer.println)
      writer.println()
      writer.println(";Variable bindings")
      nextStrs.foreach(writer.println)
      writer.println()
//      writer.println(";TLA constant initialization")
//      cinitStrs.foreach(writer.println)
//      writer.println()
      writer.println(";Initial states")
      initStrs.foreach(writer.println)
      writer.println()
      writer.println(";Transitions")
      transStrs.foreach(writer.println)
      writer.println()
      writer.println(";Invariants")
      invStrs.foreach(writer.println)
    }
  }

}

object TlaExToVMTWriter {
  val outFileName = "output.vmt"
}
