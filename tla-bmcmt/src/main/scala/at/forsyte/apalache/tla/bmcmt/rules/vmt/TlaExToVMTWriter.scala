package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir.formulas.Booleans.{And, Equiv, Exists, Forall, Impl, Neg, Or}
import at.forsyte.apalache.tla.lir.formulas.EUF._
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.{ConstT1, SetT1, StrT1, TlaConstDecl, TlaEx, TlaVarDecl, Typed}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.formulas.Ord.LtUninterpreted
import org.checkerframework.checker.units.qual.s
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
    var freeVars: Set[Variable] = Set.empty
    var uninterpLits: Set[UninterpretedLiteral] = Set.empty
    var uninterpSorts: Set[UninterpretedSort] = Set.empty

    private def addFnDef(fd: FunDef): Unit =
      fnDefs = fd :: fnDefs
    private def addVar(v: Variable): Unit =
      freeVars += v
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
        freeVars = freeVars.filterNot(v => boundVars.map(_._1).toSet.contains(v.name)) // discard bound vars
      case Exists(boundVars, body) =>
        boundVars.foreach { case (_, setSort) =>
          setSort match {
            case us: UninterpretedSort => addUS(us)
            case _                     => ()
          }
        }
        collectAll(body)
        freeVars = freeVars.filterNot(v => boundVars.map(_._1).toSet.contains(v.name))

      case LtUninterpreted(lhs, rhs) =>
        collectAll(lhs)
        collectAll(rhs)
      case v @ UninterpretedVar(_, uvSort) =>
        addVar(v)
        addUS(uvSort)
      case ul: UninterpretedLiteral => addUL(ul)
      case v: Variable              => addVar(v)
      case _                        => ()
    }
  }

  private def mkFreshVar(sort: Sort): Variable = {
    val x = gen.newName()
    mkVariable(x, sort)
  }

  // Main entry point.
  def annotateAndWrite(
      varDecls: Seq[TlaVarDecl],
      constDecls: Seq[TlaConstDecl],
      @unused cInit: Seq[(String, TlaEx)],
      initTransitions: Seq[(String, TlaEx)],
      nextTransitions: Seq[(String, TlaEx)],
      invariants: Seq[(String, TlaEx)]): Unit = {

    val writer = TermToVMTWriter

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

    val initStrs = inits.map(writer.mkVMTString)

    // Each transition in nextTransitions needs the VMT wrapper Trans
    val transitions = nextTransitions.map { case (name, ex) =>
      Trans(name, rewrite(ex))
    }

    val transStrs = transitions.map(writer.mkVMTString)

    // Each invariant in invariants needs the VMT wrapper Invar
    val invs = invariants.zipWithIndex.map { case ((name, ex), i) =>
      Invar(name, i, rewrite(ex))
    }

    val invStrs = invs.map(writer.mkVMTString)

    // Each variable v in varDecls needs the VMT binding Next(v, v')
    val nextBindings = varDecls.map { case d @ TlaVarDecl(name) =>
      val sort = TlaType1ToSortConverter.sortFromType(d.typeTag.asTlaType1())
      Next(nextName(name), mkVariable(name, sort), mkVariable(VMTprimeName(name), sort))
    }

    val nextStrs = nextBindings.map(writer.mkVMTString)

    // Variable declarations
    val smtVarDecls = varDecls.map(writer.mkSMTDecl)

    // Now we declare constants and define functions aggregated by Collector
    val collector = new Collector
    inits.foreach { i => collector.collectAll(i.initExpr) }
    transitions.foreach { t => collector.collectAll(t.transExpr) }
    invs.foreach { i => collector.collectAll(i.invExpr) }

    // Sort declaration
    val allSorts = (setConstants.values ++ collector.uninterpSorts).toSet
    val sortDecls = allSorts.map(writer.mkSortDecl)

    // Uninterpreted literal declaration and uniqueness assert
    val ulitDecls = collector.uninterpLits.map(writer.mkConstDecl)
    val disticntAsserts = allSorts.flatMap { s =>
      val litsForSortS = collector.uninterpLits.filter {
        _.sort == s
      }
      (if (litsForSortS.size > 1) Some(litsForSortS) else None).map(writer.assertDistinct)
    }

    val intLits = collector.uninterpLits.filter { _.sort == Sort.intOrderSort }

    // Create axioms for i1 < i2 < ... < in
    val sortedInts = intLits.toIndexedSeq.sortWith { case (a, b) =>
      a.s.toInt < b.s.toInt
    }
    val ltPairs = for {
      i <- 0 until sortedInts.size - 1
    } yield LtUninterpreted(sortedInts(i), sortedInts(i + 1))
    val orderAxiom = writer.axiom(".axiom_litOrder", writer.mkSMT2String(And(ltPairs: _*)))

    // TODO

    // order function construction and axioms
    val intOrderAndAxioms = {
      val sort = Sort.intOrderSort
      val fnName = writer.orderFnName
      val decl = writer.mkOrdFunDecl
      val fnSort = FunctionSort(BoolSort(), sort, sort) // (I,I) -> Bool
      val ltVar = mkVariable(fnName, fnSort)
      val irreflexivity = "irr" -> {
        val x = mkFreshVar(sort)
        // \A x \in INT_T: ~Lt(x, x)
        Forall(List((x.name, sort)), Neg(Apply(ltVar, x, x)))
      }
      val transitivity = "trans" -> {
        val x = mkFreshVar(sort)
        val y = mkFreshVar(sort)
        val z = mkFreshVar(sort)
        // \A x,y,z \in INT_T: Lt(x, y) /\ Lt(y, z) => Lt(x,z)
        Forall(List((x.name, sort), (y.name, sort), (z.name, sort)),
            Impl(And(Apply(ltVar, x, y), Apply(ltVar, y, z)), Apply(ltVar, x, z)))
      }
      val totality = "tot" -> {
        val x = mkFreshVar(sort)
        val y = mkFreshVar(sort)
        // A x,y\ in INT_T: x /= y => Lt(x,y) \/ LT (y,x)
        Forall(
            List((x.name, sort), (y.name, sort)),
            Impl(Neg(Equal(x, y)), Or(Apply(ltVar, x, y), Apply(ltVar, y, x))),
        )
      }
      val axiomStrs = Seq(irreflexivity, transitivity, totality)
        .map { case (name, formula) =>
          writer.axiom(s".axiom_$name", writer.mkSMT2String(formula))
        }
        .mkString("\n")
      s"$decl\n$axiomStrs"
    }

    // Lastly, we collect free vars generated by skolemization
    // vars (skolemized from \E f \in [A -> B])
    // or CONSTANTs can be functions too
    val varNames = varDecls.map(_.name).toSet
    val notSkolemNames = varNames ++ varNames.map(VMTprimeName)
    val freeVars = collector.freeVars.withFilter(v => !notSkolemNames.contains(v.name))
    val freeVarDecls = freeVars.map { writer.mkConstDecl }

    OutputManager.withWriterInRunDir(TlaExToVMTWriter.outFileName) { writer =>
      writer.println(";Sorts")
      sortDecls.foreach(writer.println)
      writer.println()
      writer.println(";Constants")
      ulitDecls.foreach(writer.println)
      freeVarDecls.foreach(writer.println)
      writer.println()
      disticntAsserts.foreach(writer.println)
      writer.println()
      writer.println(";Variables")
      smtVarDecls.foreach(writer.println)
      writer.println()
      writer.println(";Variable bindings")
      nextStrs.foreach(writer.println)
      writer.println()
      writer.println(";Int order")
      writer.println(intOrderAndAxioms)
      writer.println(orderAxiom)
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
