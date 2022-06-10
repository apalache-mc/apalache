package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.{TlaType1, TlaVarDecl, Typed}
import at.forsyte.apalache.tla.lir.formulas.Integers._
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.EUF._
import at.forsyte.apalache.tla.lir.formulas.Ord.LtUninterpreted
import at.forsyte.apalache.tla.lir.formulas._

/**
 * TermToVMTWriter manages the translation of Terms to strings, to be written to the final output file.
 *
 * @author
 *   Jure Kukovec
 */
object TermToVMTWriter {

  private def tr: Term => String = mkSMT2String // shorthand rename

  // And and Or translate in the same way, modulo the values in the nullary case
  private def mkAndOrArgs(head: String, onEmpty: String, args: Seq[Term]): String =
    args match {
      case Nil      => onEmpty
      case h +: Nil => mkSMT2String(h)
      case _ =>
        val argStrings = args.map { x => s"${tr(x)}" }
        s"($head ${argStrings.mkString(" ")})"
    }

  private def mkQuant(quant: String, boundVars: List[(String, Sort)], p: Term): String = {
    val pairs = boundVars.map { case (name, sort) =>
      s"($name ${sortStringForQuant(sort)})"
    }
    s"($quant (${pairs.mkString(" ")}) ${tr(p)})"
  }

  private def sortStringForQuant(sort: Sort): String =
    sort match {
      case IntSort()               => "Int"
      case BoolSort()              => "Bool"
      case UninterpretedSort(name) => name
      // We should never have function sorts or untyped in quantifiers
      case s => throw new IllegalArgumentException(s"Sort of quantified variable cannot be $s")
    }

  // In declare-fun, the syntax is (declare-fun (from1 ... fromN) to), where
  // (declare-fun () to) represents a constant declaration.
  // sortAsFn constructs a pair ("from1 ... fromN","to") from a given sort
  private def sortAsFn(sort: Sort): (String, String) = sort match {
    case FunctionSort(to, from @ _*) => (from.toList.map(sortStringForQuant).mkString(" "), sortStringForQuant(to))
    case s                           => ("", sortStringForQuant(s))
  }

  def orderFnName: String = s"__lt_${Sort.intAsUninterpretedOrderedSortName}"

  // Main entry point, does the translation recursively
  def mkSMT2String(term: Term): String =
    term match {
      case IntVar(name)                  => name
      case BoolVar(name)                 => name
      case UninterpretedVar(name, _)     => name
      case FunctionVar(name, _)          => name
      case IntLiteral(i)                 => s"$i"
      case False                         => "false"
      case True                          => "true"
      case UninterpretedLiteral(s, sort) => s"${s}_${sort.sortName}"
      case FunDef(name, _, _)            => name
      case And(args @ _*)                => mkAndOrArgs("and", "true", args)
      case Or(args @ _*)                 => mkAndOrArgs("or", "false", args)
      case Neg(x)                        => s"(not ${tr(x)})"
      case Impl(a, b)                    => s"(=> ${tr(a)} ${tr(b)})"
      case Equiv(a, b)                   => s"(= ${tr(a)} ${tr(b)})"
      case Forall(boundVars, p)          => mkQuant("forall", boundVars, p)
      case Exists(boundVars, p)          => mkQuant("exists", boundVars, p)
      case Equal(a, b)                   => s"(= ${tr(a)} ${tr(b)})"
      case Apply(fn, args @ _*)          => s"(${tr(fn)} ${args.map(tr).mkString(" ")})"
      case ITE(cond, thenTerm, elseTerm) => s"(ite ${tr(cond)} ${tr(thenTerm)} ${tr(elseTerm)})"
      case LtUninterpreted(lhs, rhs)     => s"($orderFnName ${tr(lhs)} ${tr(rhs)})"
      case x                             => throw new NotImplementedError(s"${x.getClass.getName} is not supported.")

    }

  // Constructs an SMT variable declaration from a TLA variable declaration
  def mkSMTDecl(d: TlaVarDecl): String =
    d.typeTag match {
      case Typed(tt: TlaType1) =>
        val (from, to) = sortAsFn(TlaType1ToSortConverter.sortFromType(tt))
        def mkDecl(name: String) = s"(declare-fun $name ($from) $to)"
        s"${mkDecl(d.name)}\n${mkDecl(VMTprimeName(d.name))}"

      case _ => ""
    }

  def mkOrdFunDecl: String = {
    val sortStr = sortStringForQuant(Sort.intOrderSort)
    // lt: (INT_T, INT_T) -> Bool
    s"(declare-fun $orderFnName ($sortStr $sortStr) ${sortStringForQuant(BoolSort())})"
  }

  // Constructs an SMT sort declaration for a non-parametric sort.
  def mkSortDecl(us: UninterpretedSort): String =
    s"(declare-sort ${us.sortName} 0)"

  // Constructs a base declaration and a :global annotation for VMT
  private def mkBaseAndGlobal(toSortName: String, fromSortString: String, termName: String): String = {
    val baseDecl = s"(declare-fun $termName ($fromSortString) $toSortName)"
    val globalDecl = s"(define-fun ${nextName(termName)} ($fromSortString) $toSortName (! $termName :global true))"
    s"$baseDecl\n$globalDecl"
  }

  // Constructs an SMT constant declaration for each uninterpreted literal.
  def mkConstDecl(ul: UninterpretedLiteral): String = {
    val sortName = ul.sort.sortName
    val (fromSorts, toSort) = sortAsFn(ul.sort)
    val termName = s"${ul.s}_${sortName}"
    mkBaseAndGlobal(toSort, fromSorts, termName)
  }

  // Constructs an SMT constant declaration for each function constant.
  def mkConstDecl(v: Variable): String = {
    val (from, to) = sortAsFn(v.sort)
    mkBaseAndGlobal(to, from, v.name)
  }

  // Constructs an SMT function definition from FunDef
  def mkFunDef(fd: FunDef): String = {
    val FunDef(name, args, body) = fd
    val pairs = args.map { case (name, argSort) =>
      s"($name ${sortStringForQuant(argSort)})"
    }
    val toSortString = sortStringForQuant(fd.sort.to)
    s"(define-fun $name (${pairs.mkString(" ")}) $toSortString ${tr(body)})"
  }

  def axiom(axiomName: String, s: String): String =
    s"(define-fun $axiomName () Bool (! $s :axiom true))"

  // For uninterpreted literals, we need to specify distinctness
  def assertDistinct(terms: Iterable[UninterpretedLiteral]): String =
    axiom(".axiomDistinct", s"(distinct ${terms.map(tr).mkString(" ")})")

  // Adds the VMT-specific tags, as defined by the VMTExpr wrapper
  def mkVMTString(vmtEx: VMTExpr): String =
    vmtEx match {
      case Next(name, current, next) =>
        val (froms, to) = sortAsFn(current.sort)
        val dummyNamesAndSorts = froms.zipWithIndex.map { case (sortString, i) =>
          (s"_p$i@", sortString)
        }
        val fromParis = dummyNamesAndSorts.map { case (dummyName, sortString) =>
          s"($dummyName $sortString)"
        }
        val currentStr = tr(current)
        val currentApp =
          if (dummyNamesAndSorts.isEmpty) currentStr
          else s"($currentStr ${dummyNamesAndSorts.map(_._1).mkString(" ")})"

        s"(define-fun $name (${fromParis.mkString(" ")}) ${to} (! $currentApp :next ${tr(next)}))"
      case Init(name, init)      => s"(define-fun $name () Bool (! ${tr(init)} :init true))"
      case Invar(name, idx, inv) => s"(define-fun $name () Bool (! ${tr(inv)} :invar-property $idx))"
      case Trans(name, trEx)     => s"(define-fun $name () Bool (! ${tr(trEx)} :action $name))"
    }
}
