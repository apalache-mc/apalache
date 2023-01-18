package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp.signatures.FlexibleEquality.compatible
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, PartialSignature}

/**
 * Scope-unsafe builder for VariantOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeVariantBuilder extends ProtoBuilder {

  // We borrow the LiteralBuilder to make TLA strings from name tags (Scala strings)
  private val strBuilder = new UnsafeLiteralAndNameBuilder
  private def mkTlaStr: String => TlaEx = strBuilder.str

  /**
   * {{{Variant(tagName, value): targetVariantType}}}
   * @param targetVariantType
   *   must be a variant type, where `tagName` is one of the options
   */
  def variant(tagName: String, value: TlaEx, targetVariantType: VariantT1): TlaEx = {
    require(targetVariantType.row.fieldTypes.contains(tagName),
        s"Expected variantT to be a variant type containing $tagName, found $targetVariantType.")

    val argT = targetVariantType.row.fieldTypes(tagName)

    // Knowing the tag name, we can write a custom signature:
    val partialSig: PartialSignature = {
      case Seq(StrT1, t) if compatible(t, argT) => targetVariantType
    }
    val sig = completePartial(VariantOper.variant.name, partialSig)

    BuilderUtil.composeAndValidateTypes(VariantOper.variant, sig, mkTlaStr(tagName), value)
  }

  /** {{{VariantFilter(tagName, set)}}} */
  def variantFilter(tagName: String, set: TlaEx): TlaEx = {
    // Knowing the tag name, we can write a custom signature:
    val partialSig: PartialSignature = {
      case Seq(StrT1, SetT1(VariantT1(RowT1(fields, _)))) if fields.contains(tagName) => SetT1(fields(tagName))
    }
    val sig = completePartial(VariantOper.variantFilter.name, partialSig)

    BuilderUtil.composeAndValidateTypes(VariantOper.variantFilter, sig, mkTlaStr(tagName), set)
  }

  /** {{{VariantTag(variant)}}} */
  def variantTag(variant: TlaEx): TlaEx = buildBySignatureLookup(VariantOper.variantTag, variant)

  /** {{{VariantGetOrElse(tagName, variant, defaultValue)}}} */
  def variantGetOrElse(tagName: String, variant: TlaEx, defaultValue: TlaEx): TlaEx = {
    // Knowing the tag name, we can write a custom signature:
    val partialSig: PartialSignature = {
      case Seq(StrT1, VariantT1(RowT1(fields, _)), a) if fields.get(tagName).contains(a) => a
    }
    val sig = completePartial(VariantOper.variantGetOrElse.name, partialSig)
    BuilderUtil.composeAndValidateTypes(VariantOper.variantGetOrElse, sig, mkTlaStr(tagName), variant, defaultValue)
  }

  /** {{{VariantGetUnsafe(tagName, variant)}}} */
  def variantGetUnsafe(tagName: String, variant: TlaEx): TlaEx = {
    // Knowing the tag name, we can write a custom signature:
    val partialSig: PartialSignature = {
      case Seq(StrT1, VariantT1(RowT1(fields, _))) if fields.contains(tagName) => fields(tagName)
    }
    val sig = completePartial(VariantOper.variantGetUnsafe.name, partialSig)
    BuilderUtil.composeAndValidateTypes(VariantOper.variantGetUnsafe, sig, mkTlaStr(tagName), variant)
  }
}
