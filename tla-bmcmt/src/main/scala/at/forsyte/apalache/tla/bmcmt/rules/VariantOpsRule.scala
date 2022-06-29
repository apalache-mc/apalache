package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.RecordAndVariantOps
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.VariantOper
import at.forsyte.apalache.tla.lir.values.TlaStr

/**
 * Operators on variants that let the user to construct and destruct variants, as well as filter sets of variants.
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
      case OperEx(VariantOper.variantUnwrap, _, _)       => true
      case OperEx(VariantOper.variantGetOrElse, _, _, _) => true
      case OperEx(VariantOper.variantFilter, _, _)       => true
      case _                                             => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(VariantOper.variant, ValEx(TlaStr(tagName)), valueEx) =>
        val variantT = TlaType1.fromTypeTag(ex.typeTag)
        translateVariant(state, tagName, valueEx, variantT)

      case OperEx(VariantOper.variantGetUnsafe, ValEx(TlaStr(tagName)), variantEx) =>
        // This should work independently of the tag associated with the variant.
        translateVariantGetUnsafe(state, tagName, variantEx)

      case OperEx(VariantOper.variantUnwrap, ValEx(TlaStr(tagName)), variantEx) =>
        // At this point, there is no difference between VariantGetUnsafe and VariantUnwrap.
        // The type checker has to make sure that the variant has only one option.
        assertSingletonVariant(variantEx)
        translateVariantGetUnsafe(state, tagName, variantEx)

      case OperEx(VariantOper.variantGetOrElse, ValEx(TlaStr(tagName)), variantEx, defaultEx) =>
        translateVariantGetOrElse(state, tagName, variantEx, defaultEx)

      case OperEx(VariantOper.variantFilter, ValEx(TlaStr(tagName)), setEx) =>
        translateVariantFilter(state, tagName, setEx)

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

  /**
   * Translate VariantFilter(tagName, set).
   */
  private def translateVariantFilter(
      state: SymbState,
      tagName: String,
      setEx: TlaEx): SymbState = {
    val nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
    val setCell = nextState.asCell
    variantOps.variantFilter(nextState, setCell, tagName)
  }

  // make sure that the expression is a variant that has only one option
  private def assertSingletonVariant(variantEx: TlaEx) = {
    def errorMsg(vt: TlaType1) = new TypingException(s"Expected a singleton variant, found: $vt", variantEx.ID)

    variantEx.typeTag.asTlaType1() match {
      case vt @ VariantT1(RowT1(fieldTypes, None)) =>
        if (fieldTypes.size == 1) {
          errorMsg(vt)
        }

      case vt =>
        errorMsg(vt)
    }
  }
}
