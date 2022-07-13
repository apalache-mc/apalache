package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.{StrT1, VariantT1}
import at.forsyte.apalache.tla.lir.oper.VariantOper
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap}

/**
 * Produces a SignatureMap for all variant operators
 *
 * @author
 *   Jure Kukovec
 */
object VariantOperSignatures {
  import BuilderUtil._
  import VariantOper._

  def getMap: SignatureMap = {

    // variant doesn't have a signature, because the type depends on the string value of the tag

    // variantFilter doesn't have a signature, because the type depends on the string value of the tag

    // (Variant) => Str
    val variantTagSig = signatureMapEntry(variantTag, { case Seq(_: VariantT1) => StrT1 })

    // variantGetOrElse doesn't have a signature, because the type depends on the string value of the tag

    // variantGetUnsafe doesn't have a signature, because the type depends on the string value of the tag

    Map(variantTagSig)
  }

}
