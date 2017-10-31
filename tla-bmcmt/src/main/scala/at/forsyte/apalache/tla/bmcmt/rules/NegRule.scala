package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-BOOL-NEG{1,2,3,4,5}.
  */
class NegRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.rex match {
      case TlaRex(OperEx(TlaBoolOper.not, _)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState, dir: SymbStateRewriter.SearchDirection): SymbState = {
    state.rex match {
      case TlaRex(OperEx(TlaBoolOper.not, ex: TlaEx)) =>
        state.setRex(TlaRex(rewriteNot(ex)))

      case _ =>
        throw new RewriterException("NegRule is not applicable")
    }
  }

  private def rewriteNot(root: TlaEx) = {
    root match {
      case OperEx(TlaBoolOper.or, es@_*) =>             // SE-BOOL-NEG1
        OperEx(TlaBoolOper.and, es.map(e => OperEx(TlaBoolOper.not, e)): _*)

      case OperEx(TlaBoolOper.and, es@_*) =>            // SE-BOOL-NEG2
        OperEx(TlaBoolOper.or, es.map(e => OperEx(TlaBoolOper.not, e)): _*)

      case OperEx(TlaBoolOper.implies, lhs, rhs) =>     // SE-BOOL-NEG3
        OperEx(TlaBoolOper.and,
          lhs, OperEx(TlaBoolOper.not, rhs))

      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>       // SE-BOOL-NEG4
        OperEx(TlaBoolOper.equiv,
          OperEx(TlaBoolOper.not, lhs),
          rhs)

      case OperEx(TlaBoolOper.not, e) => e              // SE-BOOL-NEG5

      case OperEx(TlaBoolOper.exists, x, set, pred) =>  // SE-BOOL-NEG6
        OperEx(TlaBoolOper.forall,
          x, set,
          OperEx(TlaBoolOper.not, pred))

      case OperEx(TlaBoolOper.forall, x, set, pred) =>  // SE-BOOL-NEG7
        OperEx(TlaBoolOper.exists,
          x, set,
          OperEx(TlaBoolOper.not, pred))

      case _ =>
        throw new RewriterException("NegRule is not applicable")
    }
  }
}
