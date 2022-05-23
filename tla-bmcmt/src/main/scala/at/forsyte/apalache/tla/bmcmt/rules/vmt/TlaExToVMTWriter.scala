package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir.formulas.Booleans.{And, Equiv, Exists, Forall, Impl, Neg, Or}
import at.forsyte.apalache.tla.lir.formulas.EUF.{Apply, Equal, FunDef, ITE, UninterpretedLiteral, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.{ConstT1, SetT1, StrT1, TlaConstDecl, TlaEx, TlaVarDecl, Typed}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
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

  // Collector is used to aggregate all function definitions, uninterpreted literals and uninterpreted sorts
  // that appear in any operator anywhere, so we can declare them in the VMT file.
  private class Collector {
    var fnDefs: List[FunDef] = List.empty
    var uninterpLits: Set[UninterpretedLiteral] = Set.empty
    var uninterpSorts: Set[UninterpretedSort] = Set.empty

    private def addFnDef(fd: FunDef): Unit =
      fnDefs = fd :: fnDefs
    private def addUL(ul: UninterpretedLiteral): Unit = {
      uninterpLits += ul
      uninterpSorts += ul.sort
    }

    private def addUS(us: UninterpretedSort): Unit =
      uninterpSorts += us

    def collectAll(t: Term): Unit = t match {
      case fd @ FunDef(_, _, body) =>
        addFnDef(fd)
        collectAll(body)
      case ITE(i, t, e) =>
        collectAll(i)
        collectAll(t)
        collectAll(e)
      case Apply(fn, args @ _*) =>
        collectAll(fn)
        args.foreach(collectAll)
      case And(args @ _*) => args.foreach(collectAll)
      case Or(args @ _*)  => args.foreach(collectAll)
      case Equiv(lhs, rhs) =>
        collectAll(lhs)
        collectAll(rhs)
      case Equal(lhs, rhs) =>
        collectAll(lhs)
        collectAll(rhs)
      case Impl(lhs, rhs) =>
        collectAll(lhs)
        collectAll(rhs)
      case Neg(arg) => collectAll(arg)
      case Forall(boundVars, body) =>
        boundVars.foreach { case (_, setSort) =>
          setSort match {
            case us: UninterpretedSort => addUS(us)
            case _                     => ()
          }
        }
        collectAll(body)
      case Exists(boundVars, body) =>
        boundVars.foreach { case (_, setSort) =>
          setSort match {
            case us: UninterpretedSort => addUS(us)
            case _                     => ()
          }
        }
        collectAll(body)
      case UninterpretedVar(_, uvSort) => addUS(uvSort)
      case ul: UninterpretedLiteral    => addUL(ul)
      case _                           => ()
    }
  }

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
    def rewrite: TlaEx => Term = rewriter.rewrite

    // Each transition in initTransitions needs the VMT wrapper Init
    val inits = initTransitions.map { case (name, ex) =>
      Init(name, rewrite(ex))
    }

    val initStrs = inits.map(TermToVMTWriter.mkVMTString)

    // Each transition in nextTransitions needs the VMT wrapper Trans
    val transitions = nextTransitions.map { case (name, ex) =>
      Trans(name, rewrite(ex))
    }

    val transStrs = transitions.map(TermToVMTWriter.mkVMTString)

    // Each invariant in invariants needs the VMT wrapper Invar
    val invs = invariants.zipWithIndex.map { case ((name, ex), i) =>
      Invar(name, i, rewrite(ex))
    }

    val invStrs = invs.map(TermToVMTWriter.mkVMTString)

    // Each variable v in varDecls needs the VMT binding Next(v, v')
    val nextBindings = varDecls.map { case d @ TlaVarDecl(name) =>
      val sort = TlaType1ToSortConverter.sortFromType(d.typeTag.asTlaType1())
      Next(nextName(name), mkVariable(name, sort), mkVariable(VMTprimeName(name), sort))
    }

    val nextStrs = nextBindings.map(TermToVMTWriter.mkVMTString)

    // Variable declarations
    val smtVarDecls = varDecls.map(TermToVMTWriter.mkSMTDecl)

    // Now we declare constants and define functions aggregated by Collector
    val collector = new Collector
    inits.foreach { i => collector.collectAll(i.initExpr) }
    transitions.foreach { t => collector.collectAll(t.transExpr) }
    invs.foreach { i => collector.collectAll(i.invExpr) }

    // Sort declaration
    val allSorts = (setConstants.values ++ collector.uninterpSorts).toSet
    val sortDecls = allSorts.map(TermToVMTWriter.mkSortDecl)

    // Uninterpreted literal declaration and uniqueness assert
    val ulitDecls = collector.uninterpLits.map(TermToVMTWriter.mkConstDecl)
    val disticntAsserts = allSorts.flatMap { s =>
      val litsForSortS = collector.uninterpLits.filter {
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
