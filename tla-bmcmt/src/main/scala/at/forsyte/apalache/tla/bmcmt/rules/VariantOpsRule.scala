package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.RecordAndVariantOps
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
  private val variantOps = new RecordAndVariantOps(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(VariantOper.variant, _, _)             => true
      case OperEx(VariantOper.variantGetUnsafe, _, _)    => true
      case OperEx(VariantOper.variantGetOrElse, _, _, _) => true
      case _                                             => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(VariantOper.variant, ValEx(TlaStr(tagName)), valueEx) =>
        val variantT = TlaType1.fromTypeTag(ex.typeTag)
        translateVariant(state, tagName, valueEx, variantT)

      case OperEx(VariantOper.variantGetUnsafe, ValEx(TlaStr(tagName)), variantEx) =>
        translateVariantGetUnsafe(state, tagName, variantEx)

      case OperEx(VariantOper.variantGetOrElse, ValEx(TlaStr(tagName)), variantEx, defaultEx) =>
        translateVariantGetOrElse(state, tagName, variantEx, defaultEx)

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

  /**
   * Translate VariantGetUnsafe(tagName, variant).
   */
  private def translateVariantGetUnsafe(
      state: SymbState,
      tagName: String,
      variantEx: TlaEx): SymbState = {
    val nextState = rewriter.rewriteUntilDone(state.setRex(variantEx))
    val variantCell = nextState.asCell
    val unsafeValueCell = variantOps.getUnsafeVariantValue(nextState.arena, variantCell, tagName)
    nextState.setRex(unsafeValueCell.toNameEx)
  }

  /**
   * Translate VariantGetOrElse(tagName, variant, defaultValue).
   */
  private def translateVariantGetOrElse(
      state: SymbState,
      tagName: String,
      variantEx: TlaEx,
      defaultEx: TlaEx): SymbState = {
    var nextState = rewriter.rewriteUntilDone(state.setRex(variantEx))
    val variantCell = nextState.asCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(defaultEx))
    val defaultValueCell = nextState.asCell
    variantOps.variantGetOrElse(nextState, variantCell, tagName, defaultValueCell)
  }
}
