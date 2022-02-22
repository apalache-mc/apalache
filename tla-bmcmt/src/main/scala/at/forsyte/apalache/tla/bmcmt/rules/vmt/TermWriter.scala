package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.{TlaConstDecl, TlaDecl, TlaType1, TlaVarDecl, TypeTag, Typed}
import at.forsyte.apalache.tla.lir.formulas.Integers._
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.EUF._
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.{BoolSort, FunctionSort, IntSort, UninterpretedSort}
import at.forsyte.apalache.tla.lir.formulas.{Sort, Term}

object TermWriter {

  private def tr: Term => String = mkSMT2String // shorthand rename

  private def mkAndOrArgs(head: String, onEmpty: String, args: Seq[Term]): String =
    args match {
      case Nil      => onEmpty
      case h +: Nil => mkSMT2String(h)
      case _ =>
        val argStrings = args.map { x => s"${tr(x)}" }
        s"($head ${argStrings.mkString(" ")})"
    }

  private def mkQuant(
      quant: String,
      x: String,
      s: String,
      p: Term): String =
    s"($quant (($x $s)) ${tr(p)})"

  private def sortStringForQuant(sort: Sort): String =
    sort match {
      case IntSort()               => "Int"
      case BoolSort()              => "Bool"
      case UninterpretedSort(name) => name
      // We should never have function sorts or untyped in quantifiers
      case s => throw new IllegalArgumentException(s"Sort of quantified variable cannot be $s")
    }

  private def sortAsFn(sort: Sort): (List[String], String) = sort match {
    case FunctionSort(to, from @ _*) => (from.toList.map(sortStringForQuant), sortStringForQuant(to))
    case s                           => (List.empty, sortStringForQuant(s))
  }

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
      case Forall(x, s, p)               => mkQuant("forall", x, sortStringForQuant(s), p)
      case Exists(x, s, p)               => mkQuant("exists", x, sortStringForQuant(s), p)
      case Equal(a, b)                   => s"(= ${tr(a)} ${tr(b)})"
      case Apply(fn, args @ _*)          => s"(${tr(fn)} ${args.map(tr).mkString(" ")})"
      case ITE(cond, thenTerm, elseTerm) => s"(ite ${tr(cond)} ${tr(thenTerm)} ${tr(elseTerm)})"
      // Le
      // Lt
      // Ge
      // Gt
      case x => throw new NotImplementedError(s"${x.getClass} is not supported yet.")

    }

  def mkSMTDecl(d: TlaVarDecl): String =
    d.typeTag match {
      case Typed(tt: TlaType1) =>
        val (froms, to) = sortAsFn(TermAndSortCaster.sortFromType(tt))
        s"(declare-fun ${d.name} (${froms.mkString(" ")}) $to)"
      case _ => ""
    }

  def mkSortDecl(us: UninterpretedSort): String =
    s"(declare-sort ${us.sortName} 0)"

  def mkConstDecl(ul: UninterpretedLiteral): String =
    s"(declare-fun ${ul.s}_${ul.sort.sortName} () ${ul.sort.sortName})"

  def mkFunDef(fd: FunDef): String = {
    val FunDef(name, args, body) = fd
    val pairs = args.map { case (name, argSort) =>
      s"($name ${sortStringForQuant(argSort)})"
    }
    val toSortString = sortStringForQuant(fd.sort.to)
    s"(define-fun $name (${pairs.mkString(" ")}) $toSortString ${tr(body)})"
  }

  def mkVMTString(vmtEx: VMTExpr): String =
    vmtEx match {
      case Next(name, current, next) =>
        val (froms, to) = sortAsFn(current.sort)
        val fromParis = froms.zipWithIndex.map { case (sortString, i) =>
          val dummyName = s"_p$i@"
          s"($dummyName $sortString)"
        }

        s"(define-fun $name (${fromParis.mkString(" ")}) ${to} (! ${tr(current)} :next ${tr(next)}))"
      case Init(name, init)      => s"(define-fun $name () Bool (! ${tr(init)} :init true))"
      case Invar(name, idx, inv) => s"(define-fun $name () Bool (! ${tr(inv)} :invar-property $idx))"
      case Trans(name, trEx)     => s"(define-fun $name () Bool (! ${tr(trEx)} :trans true))"
    }
}
