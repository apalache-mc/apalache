package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, PartialSignature}

import scala.collection.immutable.SortedMap

/**
 * Scope-unsafe builder for VariantOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeVariantBuilder extends ProtoBuilder {

  /** Checks that the tag is a TLA string, and extracts the string value if that is the case. */
  private def checkTagAndGetName(tag: TlaEx): String = {
    require(tag match {
          case ValEx(_: TlaStr) => true
          case _                => false
        }, s"Expected tag to be a TLA+ string, found $tag.")
    val ValEx(TlaStr(tagName)) = tag
    tagName
  }

  /**
   * {{{Variant(tag, value): variantT}}}
   * @param tag
   *   must be a TLA+ string
   * @param variantT
   *   must be a variant type, where `tag` is one of the options
   */
  def variant(tag: TlaEx, value: TlaEx, variantT: TlaType1): TlaEx = {
    val tagName = checkTagAndGetName(tag)
    require(variantT match {
          case VariantT1(RowT1(keys, _)) => keys.contains(tagName)
        }, s"Expected variantT to be a variant type containing $tagName, found $variantT.")

    OperEx(VariantOper.variant, tag, value)(Typed(variantT))
  }

  /**
   * {{{VariantFilter(tag, set)}}}
   * @param tag
   *   must be a TLA+ string
   */
  def variantFilter(tag: TlaEx, set: TlaEx): TlaEx = {
    val tagName = checkTagAndGetName(tag)

    // Knowing the tag name, we can write a custom signature:
    val partialSig: PartialSignature = {
      case Seq(StrT1, SetT1(VariantT1(RowT1(fields, _)))) if fields.contains(tagName) => SetT1(fields(tagName))
    }
    val sig = completePartial(VariantOper.variantFilter.name, partialSig)

    BuilderUtil.composeAndValidateTypes(VariantOper.variantFilter, sig, tag, set)
  }

  /** {{{VariantTag(v)}}} */
  def variantTag(v: TlaEx): TlaEx = buildBySignatureLookup(VariantOper.variantTag, v)

  /** {{{VariantTag(v)}}} */
}
