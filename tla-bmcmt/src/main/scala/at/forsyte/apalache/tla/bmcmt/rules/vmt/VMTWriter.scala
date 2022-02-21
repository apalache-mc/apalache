package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir.formulas.Booleans.{And, Equiv, Exists, Forall, Impl, Neg, Or}
import at.forsyte.apalache.tla.lir.formulas.EUF.{Apply, Equal, FunDef, ITE, UninterpretedLiteral, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.UninterpretedSort
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir.{ConstT1, NameEx, SetT1, StrT1, TlaConstDecl, TlaEx, TlaVarDecl, Typed}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

class VMTWriter(gen: UniqueNameGenerator) {

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
        args foreach collectAll
      case And(args @ _*) => args foreach collectAll
      case Or(args @ _*)  => args foreach collectAll
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

  private def collectFromLst(lst: Traversable[Term], init: List[FunDef] = List.empty): List[FunDef] =
    lst.map(collectDefs).foldLeft(init) { _ ++ _ }

  private def collectDefs(t: Term): List[FunDef] = t match {
    case fd @ FunDef(_, _, body) => fd :: collectDefs(body)
    case ITE(i, t, e) =>
      collectDefs(i) ++ collectDefs(t) ++ collectDefs(e)
    case Apply(fn, args @ _*) => collectFromLst(args, collectDefs(fn))
    case And(args @ _*)       => collectFromLst(args)
    case Or(args @ _*)        => collectFromLst(args)
    case Equiv(lhs, rhs)      => collectDefs(lhs) ++ collectDefs(rhs)
    case Equal(lhs, rhs)      => collectDefs(lhs) ++ collectDefs(rhs)
    case Impl(lhs, rhs)       => collectDefs(lhs) ++ collectDefs(rhs)
    case Neg(arg)             => collectDefs(arg)
    case Forall(_, _, body)   => collectDefs(body)
    case Exists(_, _, body)   => collectDefs(body)
    case _                    => List.empty
  }

  def annotateAndWrite(
      varDecls: Seq[TlaVarDecl], constDecls: Seq[TlaConstDecl], cInit: Seq[(String, TlaEx)],
      initTransitions: Seq[(String, TlaEx)], nextTransitions: Seq[(String, TlaEx)], invariants: Seq[(String, TlaEx)],
  ): Unit = {
    val setConstants = constDecls
      .map { d => (d.name, d.typeTag) }
      .collect {
        case (name, Typed(SetT1(ConstT1(sortName)))) => (name, UninterpretedSort(sortName))
        case (name, Typed(SetT1(StrT1())))           => (name, UninterpretedSort(StrT1().toString))
      }
      .toMap[String, UninterpretedSort]

    val rewriter = new RewriterImpl(setConstants, gen)

    val cinits = cInit map { case (_, ex) =>
      rewriter.rewrite(ex)
    }
    val cinitStrs = cinits map TermWriter.mkSMT2String

    val inits = initTransitions map { case (name, ex) =>
      Init(name, rewriter.rewrite(ex))
    }

    val initStrs = inits map TermWriter.mkVMTString

    val transitions = nextTransitions map { case (name, ex) =>
      Trans(name, rewriter.rewrite(ex))
    }

    val transStrs = transitions map TermWriter.mkVMTString

    val invs = invariants.zipWithIndex map { case ((name, ex), i) =>
      Invar(name, i, rewriter.rewrite(ex))
    }

    val invStrs = invs map TermWriter.mkVMTString

    val nextBindings = varDecls map { case d @ TlaVarDecl(name) =>
      val nameEx = NameEx(name)(d.typeTag)
      Next(nextName(name), ValueRule.termFromNameEx(nameEx), ValueRule.termFromNameEx(renamePrimesForVMT(nameEx)))
    }

    val nextStrs = nextBindings map TermWriter.mkVMTString

    val collector = new Collector
    inits foreach { i => collector.collectAll(i.initExpr) }
    transitions foreach { t => collector.collectAll(t.transExpr) }
    invs foreach { i => collector.collectAll(i.invExpr) }

    val fnDefs = collector.fnDefs map {
      TermWriter.mkFunDef
    }

    val sortDecls = (setConstants.values ++ collector.uninterpSorts).toSet map TermWriter.mkSortDecl
    val ulitDecls = collector.uninterpLits map TermWriter.mkConstDecl

    val smtVarDecls = varDecls map TermWriter.mkSMTDecl

    OutputManager.withWriterInRunDir(VMTWriter.outFileName) { writer =>
      writer.println(";Sorts")
      sortDecls foreach writer.println
      writer.println()
      writer.println(";Constants")
      ulitDecls foreach writer.println
      writer.println()
      writer.println(";Variables")
      smtVarDecls foreach writer.println
      writer.println()
      writer.println(";Intermediate function definitions")
      fnDefs foreach writer.println
      writer.println()
      writer.println(";Variable bindings")
      nextStrs foreach writer.println
      writer.println()
      writer.println(";TLA constant initialization")
      cinitStrs foreach writer.println
      writer.println()
      writer.println(";Initial states")
      initStrs foreach writer.println
      writer.println()
      writer.println(";Transitions")
      transStrs foreach writer.println
      writer.println()
      writer.println(";Invariants")
      invStrs foreach writer.println
    }
  }

}

object VMTWriter {
  val outFileName = "output.vmt"
}
