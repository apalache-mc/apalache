package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp.{Applicative, BuilderUtil, PartialSignature}

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
   * {{{Variant(tag, value)}}}
   * @param tag
   *   must be a TLA+ string
   */
  def variant(tag: TlaEx, value: TlaEx): TlaEx = {
    val tagName = checkTagAndGetName(tag)
    val rowT = RowT1(tagName -> value.typeTag.asTlaType1())

    // For any a, returns tagName(a), so we don't need type calculus
    OperEx(VariantOper.variant, tag, value)(Typed(VariantT1(rowT)))
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
      case Seq(StrT1, SetT1(VariantT1(row))) if row.fieldTypes.contains(tagName) => SetT1(row.fieldTypes(tagName))
    }
    val sig = completePartial(VariantOper.variantFilter.name, partialSig)

    BuilderUtil.composeAndValidateTypes(VariantOper.variantFilter, sig, tag, set)
  }

  /** {{{VariantTag(v)}}} */
  def variantTag(v: TlaEx): TlaEx = buildBySignatureLookup(VariantOper.variantTag, v)
}
