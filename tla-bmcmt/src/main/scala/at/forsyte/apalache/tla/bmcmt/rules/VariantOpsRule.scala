package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, RecordAndVariantOps}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.VariantOper
import at.forsyte.apalache.tla.lir.values.TlaStr

/**
 * Variant operations: Variant, VariantFilter, VariantMatch, VariantGet.
 *
 * @author
 *   Igor Konnov
 */
class VariantOpsRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new CherryPick(rewriter)
  private val variantOps = new RecordAndVariantOps(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(VariantOper.variant, _, _) => true
      case _                                 => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(VariantOper.variant, ValEx(TlaStr(tagName)), valueEx) =>
        val variantT = TlaType1.fromTypeTag(ex.typeTag)
        translateVariant(state, tagName, valueEx, variantT)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  /**
   * Translate Variant(tagName, value).
   */
  private def translateVariant(
      state: SymbState,
      tagName: String,
      valueEx: TlaEx,
      variantT: TlaType1): SymbState = {
    val nextState = rewriter.rewriteUntilDone(state.setRex(valueEx))
    val valueCell = nextState.asCell
    variantOps.makeVariant(nextState, variantT, tagName, valueCell)
  }
}
