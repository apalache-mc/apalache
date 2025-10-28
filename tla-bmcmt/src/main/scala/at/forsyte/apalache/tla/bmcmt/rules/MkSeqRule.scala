package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.ProtoSeqOps
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{ApalacheInternalOper, ApalacheOper, TlaArithOper}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.pp.{Inliner, TlaInputError}

import scala.collection.immutable.SortedMap

/**
 * Rewriting rule for MkSeq. This rule is similar to [[FoldSeqRule]].
 *
 * @author
 *   Igor Konnov
 */
class MkSeqRule(rewriter: SymbStateRewriter, renaming: IncrementalRenaming) extends RewritingRule {
  private val proto = new ProtoSeqOps(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = symbState.ex match {
    // match the internal representation of lambda expressions or embedded calls
    case OperEx(ApalacheOper.mkSeq, _, LetInEx(NameEx(appName), TlaOperDecl(operName, params, _))) =>
      appName == operName && params.size == 1
    case _ => false
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(ApalacheOper.mkSeq, lenEx, LetInEx(NameEx(_), opDecl)) =>
      val operT = opDecl.typeTag.asTlaType1()
      val elemT = operT match {
        case OperT1(Seq(IntT1), et) => et
        case tp                     =>
          // this case should be found by the type checker
          val msg = "Expected an operator of type Int => <elem type>. Found: " + tp
          throw new TlaInputError(msg, Some(opDecl.ID))
      }

      // expressions are transient, we don't need tracking
      val inliner = new Inliner(new IdleTracker, renaming)
      // We can make the scope directly, since InlinePass already ensures all is well.
      val seededScope: Inliner.Scope = SortedMap(opDecl.name -> opDecl)

      def mkElem(state: SymbState, index: Int): (SymbState, ArenaCell) = {
        // get the cell for the index
        val (newArena, indexCell) = rewriter.intValueCache.create(state.arena, index)
        // elem = A(indexCell)
        val appEx = tla.appOp(tla.name(opDecl.name).as(operT), indexCell.toNameEx.as(IntT1))
        val inlinedEx = inliner.transform(seededScope)(appEx.as(elemT))
        // simply rewrite the body of the definition with the index cell as the argument
        val nextState = rewriter.rewriteUntilDone(state.setArena(newArena).setRex(inlinedEx))
        (nextState, nextState.asCell)
      }

      // create the proto sequence with the help of the user-defined operator
      val (capState, capacity) = computeCapacity(state, lenEx)
      var nextState = proto.make(capState, capacity, mkElem)
      val protoSeq = nextState.asCell
      // create the sequence on top of the proto sequence
      nextState = nextState.updateArena(_.appendCell(IntT1))
      val lenCell = nextState.arena.topCell
      rewriter.solverContext.assertGroundExpr(tla.eql(lenCell.toNameEx.as(IntT1), tla.int(capacity)).as(BoolT1))
      proto.mkSeq(nextState, SeqT1(elemT), protoSeq, lenCell)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  // Extract capacity from a constant expression that may contain a call to __ApalacheSeqCapacity.
  // The main use for this method is internal rewiring, e.g., in `__rewire_sequences_ext_in_apalache.tla`.
  // This code somewhat duplicates ConstSimplifier.
  private def computeCapacity: (SymbState, TlaEx) => (SymbState, Int) = {
    case (state, ValEx(TlaInt(n))) if n.isValidInt && n >= 0 =>
      (state, n.toInt)

    case (_, e @ ValEx(TlaInt(n))) if !n.isValidInt || n < 0 =>
      val msg = s"Expected an integer in the range [0, ${Int.MaxValue}]. Found: $n"
      throw new TlaInputError(msg, Some(e.ID))

    case (state, OperEx(ApalacheInternalOper.apalacheSeqCapacity, seq)) =>
      // rewrite the sequence expression and extract its constant capacity
      val nextState = rewriter.rewriteUntilDone(state.setRex(seq))
      val (_, _, capacity) = proto.unpackSeq(nextState.arena, nextState.asCell)
      (nextState, capacity)

    case (state, OperEx(TlaArithOper.plus, left, right)) =>
      val (lstate, lcap) = computeCapacity(state, left)
      val (rstate, rcap) = computeCapacity(lstate, right)
      val sumAsBigInt = BigInt(lcap) + rcap
      if (!sumAsBigInt.isValidInt) {
        throw new IllegalArgumentException("Overflow in sequence capacity: " + sumAsBigInt)
      }
      (rstate, sumAsBigInt.toInt)

    case (state, OperEx(TlaArithOper.minus, left, right)) =>
      val (lstate, lcap) = computeCapacity(state, left)
      val (rstate, rcap) = computeCapacity(lstate, right)
      val diffAsBigInt = BigInt(lcap) - rcap
      if (!diffAsBigInt.isValidInt) {
        throw new IllegalArgumentException("Underflow in sequence capacity: " + diffAsBigInt)
      }
      (rstate, diffAsBigInt.toInt)

    case (state, OperEx(TlaArithOper.mult, left, right)) =>
      val (lstate, lcap) = computeCapacity(state, left)
      val (rstate, rcap) = computeCapacity(lstate, right)
      val prodAsBigInt = BigInt(lcap) * rcap
      if (!prodAsBigInt.isValidInt) {
        throw new IllegalArgumentException("Overflow in sequence capacity: " + prodAsBigInt)
      }
      (rstate, prodAsBigInt.toInt)

    case (state, OperEx(TlaArithOper.div, left, right)) =>
      val (lstate, lcap) = computeCapacity(state, left)
      val (rstate, rcap) = computeCapacity(lstate, right)
      (rstate, lcap / rcap)

    case (_, unexpectedEx) =>
      val msg = "Expected a constant integer expression. Found: " + unexpectedEx
      throw new TlaInputError(msg, Some(unexpectedEx.ID))

  }
}
