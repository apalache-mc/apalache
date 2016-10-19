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

  /** the standard \subseteq operator */
  val subseteq = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\subseteq"
  }

  /** the standard \subset operator */
  val subset = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\subset"
  }

  /** the standard \supset operator */
  val supset = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\supset"
  }

  /** the standard \supseteq operator */
  val supseteq = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\supseteq"
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

  /** TLA SUBSET, i.e., the set of all subsets (of a given set).
    We use the name 'powerset' to avoid confusion with \subset and \subseteq.
    */
  val powerset = new TlaSetOper {
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
