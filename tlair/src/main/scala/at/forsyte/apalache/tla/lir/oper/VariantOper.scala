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
  object filterByTag extends VariantOper {
    override def name: String = "Variants!FilterByTag"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * Match a variant by tag.
   */
  object matchTag extends VariantOper {
    override def name: String = "Variants!MatchTag"

    override def arity: OperArity = FixedArity(4)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * Match a single variant.
   */
  object matchOnly extends VariantOper {
    override def name: String = "Variants!MatchOnly"

    override def arity: OperArity = FixedArity(3)

    override val precedence: (Int, Int) = (100, 100)
  }
}
