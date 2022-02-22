package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir.formulas.Booleans.{And, BoolExpr, Equiv, Exists, Forall, Impl, Neg, Or}
import at.forsyte.apalache.tla.lir.formulas.EUF.{Apply, Equal, FunDef, ITE, UninterpretedLiteral, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.{BoolSort, UninterpretedSort}
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir.{ConstT1, NameEx, SetT1, StrT1, TlaConstDecl, TlaEx, TlaVarDecl, Typed}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1

/**
 * VMTWriter handles the last step of transpiling. It takes the disassembled module (extracted init, next, inv, etc.)
 * and determines how TermWriter gets called, then writes the output to the specified file.
 *
 * @author
 *   Jure Kukovec
 */
class VMTWriter(gen: UniqueNameGenerator) {

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
      case Forall(_, setSort, body) =>
        setSort match {
          case us: UninterpretedSort => addUS(us)
          case _                     => ()
        }
        collectAll(body)
      case Exists(_, setSort, body) =>
        setSort match {
          case us: UninterpretedSort => addUS(us)
          case _                     => ()
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
      cInit: Seq[(String, TlaEx)],
      initTransitions: Seq[(String, TlaEx)],
      nextTransitions: Seq[(String, TlaEx)],
      invariants: Seq[(String, TlaEx)]): Unit = {

    // First, we parse the constant declarations, to extract all restricted sets, i.e.,
    // constants typed with SetT1(ConsT1(_))
    val setConstants = constDecls
      .map { d => (d.name, d.typeTag) }
      .collect {
        case (name, Typed(SetT1(ConstT1(sortName)))) => (name, UninterpretedSort(sortName))
        case (name, Typed(SetT1(StrT1())))           => (name, UninterpretedSort(StrT1().toString))
      }
      .toMap[String, UninterpretedSort]

    val rewriter = new RewriterImpl(setConstants, gen)

    // Not sure what to do with CInits yet
//    val cinits = cInit.map { case (_, ex) =>
//      rewriter.rewrite(ex)
//    }
//    val cinitStrs = cinits.map(TermWriter.mkSMT2String)

    def boolCast: TlaEx => BoolExpr = TermAndSortCaster.rewriteAndCast[BoolExpr](rewriter, BoolSort())

    // Each transition in initTransitions needs the VMT wrapper Init
    val inits = initTransitions.map { case (name, ex) =>
      Init(name, boolCast(ex))
    }

    val initStrs = inits.map(TermWriter.mkVMTString)

    // Each transition in nextTransitions needs the VMT wrapper Trans
    val transitions = nextTransitions.map { case (name, ex) =>
      Trans(name, boolCast(ex))
    }

    val transStrs = transitions.map(TermWriter.mkVMTString)

    // Each invariant in invariants needs the VMT wrapper Invar
    val invs = invariants.zipWithIndex.map { case ((name, ex), i) =>
      Invar(name, i, boolCast(ex))
    }

    val invStrs = invs.map(TermWriter.mkVMTString)

    // Each variable v in varDecls needs the VMT binding Next(v, v')
    val nextBindings = varDecls.map { case d @ TlaVarDecl(name) =>
      val sort = TermAndSortCaster.sortFromType(d.typeTag.asTlaType1())
      Next(nextName(name), mkVariable(name, sort), mkVariable(VMTprimeName(name), sort))
    }

    val nextStrs = nextBindings.map(TermWriter.mkVMTString)

    // Variable declarations
    val smtVarDecls = varDecls.map(TermWriter.mkSMTDecl)

    // Now we declare constants and define functions aggregated by Collector
    val collector = new Collector
    inits.foreach { i => collector.collectAll(i.initExpr) }
    transitions.foreach { t => collector.collectAll(t.transExpr) }
    invs.foreach { i => collector.collectAll(i.invExpr) }

    // Function definitions
    val fnDefs = collector.fnDefs.map {
      TermWriter.mkFunDef
    }

    // Sort declaration
    val allSorts = (setConstants.values ++ collector.uninterpSorts).toSet
    val sortDecls = allSorts.map(TermWriter.mkSortDecl)

    // Uninterpreted literal declaration and uniqueness assert
    val ulitDecls = collector.uninterpLits.map(TermWriter.mkConstDecl)
    val disticntAsserts = allSorts.flatMap { s =>
      val litsForSortS = collector.uninterpLits.filter {
        _.sort == s
      }
      (if (litsForSortS.size > 1) Some(litsForSortS) else None).map(TermWriter.assertDistinct)
    }

    OutputManager.withWriterInRunDir(VMTWriter.outFileName) { writer =>
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
      writer.println(";Intermediate function definitions")
      fnDefs.foreach(writer.println)
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

object VMTWriter {
  val outFileName = "output.vmt"
}
