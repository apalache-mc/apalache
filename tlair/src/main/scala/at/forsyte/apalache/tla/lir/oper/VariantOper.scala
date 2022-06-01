package at.forsyte.apalache.tla.lir.oper

/**
 * Operators over variants.
 *
 * @author
 *   Igor Konnov
 */
abstract class VariantOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

object VariantOper {

  /**
   * Variant constructor.
   */
  object variant extends VariantOper {
    override def name: String = "Variants!Variant"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * Set filter over variants.
   */
  object variantFilter extends VariantOper {
    override def name: String = "Variants!VariantFilter"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * Match a variant by tag.
   */
  object variantMatch extends VariantOper {
    override def name: String = "Variants!VariantMatch"

    override def arity: OperArity = FixedArity(4)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * Match a single variant.
   */
  object variantGet extends VariantOper {
    override def name: String = "Variants!VariantGet"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }
}
