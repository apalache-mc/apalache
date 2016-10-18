package at.forsyte.apalache.tla.lir.oper

/**
 * Set operators.
 */
abstract class TlaSetOper extends TlaOper {
  override def level: Level.Value = Level.State
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaSetOper {
  val in = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\in"
  }

  val notin = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\notin"
  }

  val cup = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\cup"
  }

  val cap = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\cap"
  }

  val subseteq = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\subseteq"
  }

  val setminus = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\setminus"
  }

  /** A restricted set comprehension: { x \in S : p } */
  val filter = new TlaSetOper {
    override val arity = FixedArity(3)
    override val name = "filter"
  }

  /** A set replacement: { e: x \in S } */
  val map = new TlaSetOper {
    override val arity = FixedArity(3)
    override val name = "map"
  }

  /** TLA SUBSET, i.e., the set of all subsets (of a given set) */
  val subset = new TlaSetOper {
    override val arity = FixedArity(1)
    override val name = "SUBSET"
  }

  /** TLA UNION, i.e., the union of all elements (of a given set).

    WARNING: use it when you really need it. In all other cases, use \cup.
    */
  val union = new TlaSetOper {
    override val arity = FixedArity(1)
    override val name = "UNION"
  }
}
