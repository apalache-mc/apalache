package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.formulas.Integers._
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.EUF._
import at.forsyte.apalache.tla.lir.formulas.Term

object TermWriter {

  private def mkAndOrArgs(head: String, onEmpty: String, args: Seq[Term]): String =
    args match {
      case Nil      => onEmpty
      case h +: Nil => mkSMT2String(h)
      case _ =>
        val argStrings = args map { x => s"${mkSMT2String(x)}" }
        s"($head ${argStrings.mkString(" ")})"
    }

  private def mkQuant(quant: String, x: String, s: String, p: Term): String =
    s"($quant (($x $s)) ${mkSMT2String(p)})"

  def mkSMT2String(term: Term): String =
    term match {
      case IntVar(name)               => name
      case BoolVar(name)              => name
      case UninterpretedVar(name, _)  => name
      case IntLiteral(i)              => s"$i"
      case False                      => "false"
      case True                       => "true"
      case UninterpretedLiteral(s, _) => s
      case And(args @ _*)             => mkAndOrArgs("and", "true", args)
      case Or(args @ _*)              => mkAndOrArgs("or", "false", args)
      case Neg(x)                     => s"(not ${mkSMT2String(x)})"
      case Impl(a, b)                 => s"(=> ${mkSMT2String(a)} ${mkSMT2String(b)})"
      case Equiv(a, b)                => s"(= ${mkSMT2String(a)} ${mkSMT2String(b)})"
      case Forall(x, s, p)            => mkQuant("forall", x, s.sortName, p)
      case Exists(x, s, p)            => mkQuant("exists", x, s.sortName, p)
      case Equal(a, b)                => s"(= ${mkSMT2String(a)} ${mkSMT2String(b)})"
      case Apply(fn, args @ _*)       => s"(${mkSMT2String(fn)} ${args.map(mkSMT2String).mkString(" ")})"
      // ITE
      // Le
      // Lt
      // Ge
      // Gt
      case x => x.toString // not supported yet

    }

  def mkVMTString(vmtEx: VMTExpr): String =
    vmtEx match {
      case Next(name, current, next) => s"(define-fun $name () ${current.sort.sortName} (! $current :next $next))"
      case Init(name, init)          => s"(define-fun $name () Bool (! ${mkSMT2String(init)} :init true))"
      case Invar(name, idx, inv)     => s"(define-fun $name () Bool (! ${mkSMT2String(inv)} :invar-property $idx))"
      case Trans(name, tr)           => s"(define-fun $name () Bool (! ${mkSMT2String(tr)} :trans true))"
    }
}
