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
  private val unsafeBuilder = new UnsafeVariantBuilder {}

  /**
   * {{{Variant(tagName, value): targetVariantType}}}
   * @param targetVariantType
   *   must be a variant type, where `tagName` is one of the options
   */
  def variant(tagName: String, value: TBuilderInstruction, targetVariantType: VariantT1): TBuilderInstruction =
    value.map(unsafeBuilder.variant(tagName, _, targetVariantType))

  /** {{{VariantFilter(tagName, set)}}} */
  def variantFilter(tagName: String, set: TBuilderInstruction): TBuilderInstruction =
    set.map(unsafeBuilder.variantFilter(tagName, _))

  /** {{{VariantTag(variant)}}} */
  def variantTag(variant: TBuilderInstruction): TBuilderInstruction = variant.map(unsafeBuilder.variantTag)

  /** {{{VariantGetOrElse(tagName, variant, defaultValue)}}} */
  def variantGetOrElse(
      tagName: String,
      variant: TBuilderInstruction,
      defaultValue: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(variant, defaultValue)(unsafeBuilder.variantGetOrElse(tagName, _, _))

  /** {{{VariantGetUnsafe(tagName, variant)}}} */
  def variantGetUnsafe(tagName: String, variant: TBuilderInstruction): TBuilderInstruction =
    variant.map(unsafeBuilder.variantGetUnsafe(tagName, _))
}
