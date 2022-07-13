package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir.VariantT1
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeVariantBuilder

/**
 * Scope-safe builder for VariantOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait VariantBuilder {
  private val unsafeBuilder = new UnsafeVariantBuilder

  /**
   * {{{Variant(tagName, value): variantT}}}
   * @param variantT
   *   must be a variant type, where `tagName` is one of the options
   */
  def variant(tagName: String, value: TBuilderInstruction, variantT: VariantT1): TBuilderInstruction =
    value.map(unsafeBuilder.variant(tagName, _, variantT))

  /** {{{VariantFilter(tagName, set)}}} */
  def variantFilter(tagName: String, set: TBuilderInstruction): TBuilderInstruction =
    set.map(unsafeBuilder.variantFilter(tagName, _))

  /** {{{VariantTag(v)}}} */
  def variantTag(v: TBuilderInstruction): TBuilderInstruction = v.map(unsafeBuilder.variantTag)

  /** {{{VariantGetOrElse(tagName, v, default)}}} */
  def variantGetOrElse(tagName: String, v: TBuilderInstruction, default: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(v, default)(unsafeBuilder.variantGetOrElse(tagName, _, _))

  /** {{{VariantGetUnsafe(tagName, v)}}} */
  def variantGetUnsafe(tagName: String, v: TBuilderInstruction): TBuilderInstruction =
    v.map(unsafeBuilder.variantGetUnsafe(tagName, _))
}
