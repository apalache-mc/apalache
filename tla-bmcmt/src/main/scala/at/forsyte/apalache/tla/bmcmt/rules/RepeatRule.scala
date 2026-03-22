package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.pp.Inliner
import at.forsyte.apalache.tla.types.{tlaU => tla}

import scala.collection.immutable.SortedMap

/**
 * Rewriting rule for Repeat. This rule is similar to [[FoldSeqRule]].
 *
 * This rule is more efficient than the fold- rules, because it does not require an underlying data structure (Seq or
 * Set). In particular, folding over 1..N, despite the overapproximation being tight by construction, still introduces
 * O(N*N) constraints, since the SMT solver must assert element uniqueness (i /= j for all i,j \in 1..N). OTOH,
 * RepeatRule consumes 1..N in the canonical order natively as a 1.to(N) in Scala.
 *
 * @author
 *   Jure Kukovec
 */
class RepeatRule(rewriter: SymbStateRewriter, renaming: IncrementalRenaming) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(ApalacheOper.repeat, LetInEx(NameEx(appName), TlaOperDecl(operName, params, _)), _, _) =>
        appName == operName && params.size == 2
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    // assume isApplicable
    case ex @ OperEx(ApalacheOper.repeat, LetInEx(NameEx(_), opDecl), boundEx, baseEx) =>
      boundEx match {
        case ValEx(TlaInt(n)) if n.isValidInt && n.toInt >= 0 =>
          // rewrite baseEx to its final cell form
          val baseState = rewriter.rewriteUntilDone(state.setRex(baseEx))

          // We need the type signature. The signature of Repeat is
          // \A a : ((a,Int) => a, Int, a) => a
          // so the operator type must be (a,Int) => a
          val a = TlaType1.fromTypeTag(baseEx.typeTag)
          val opT = OperT1(Seq(a, IntT1), a)
          // sanity check
          TlaType1.fromTypeTag(opDecl.typeTag) match {
            case `opT`   => // all good
            case badType =>
              val msg = s"FoldSet argument ${opDecl.name} should have the tag $opT, found $badType."
              throw new TypingException(msg, opDecl.ID)
          }

          // expressions are transient, we don't need tracking
          val inliner = new Inliner(new IdleTracker, renaming)
          // We can make the scope directly, since InlinePass already ensures all is well.
          val seededScope: Inliner.Scope = SortedMap(opDecl.name -> opDecl)

          // To implement the Repeat rule, we generate a sequence of cells.
          // At each step, we perform one application of the operator
          // defined by `opDecl` to the previous partial result,
          // and pass the iteration index as the second parameter
          (1 to n.toInt).foldLeft(baseState) { case (partialState, i) =>
            // partialState currently holds the cell representing the previous application step
            val oldResultCell = partialState.asCell

            // First, we inline the operator application, with cell names as parameters
            val appEx = tla.appOp(
                tla.name(opDecl.name, opT),
                oldResultCell.toBuilder,
                tla.int(i),
            )

            val inlinedEx = inliner.transform(seededScope)(appEx)
            rewriter.rewriteUntilDone(partialState.setRex(inlinedEx))
          }
        case _ =>
          throw new RewriterException("Apalache!Repeat expects a constant positive integer. Found: " + boundEx, ex)
      }
    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }
}
