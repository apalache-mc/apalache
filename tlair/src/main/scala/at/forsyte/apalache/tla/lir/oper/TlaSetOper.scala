package at.forsyte.apalache.tla.lir.oper

/**
 * Set operators.
 */
abstract class TlaSetOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaSetOper {
  /**
    Define a set by enumerating its elements, i.e., {e_1, ..., e_k}
    Note that we explicitly forbid to construct an empty set using this operator.
    To construct an empty set, use emptySet.
   */
  val enumSet = new TlaSetOper {
    override val arity = AnyArity() // FIX: we allow zero arguments as well
    override val name = "{...}"
  }

  /**
   * Construct a set of functions from a set S to a set T, i.e., [S -> T].
   */
  val funSet = new TlaSetOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "[S -> T]"
  }

  /**
    * Construct a set of records, e.g., [ f_1: S_1, ..., f_k: S_k ].
    * The order of the arguments is as follows: (f_1, S_1, ..., f_k, S_k).
    * The field names f_1, ..., f_k are string constants,
    * that is, ValEx(TlaStr("...")) and not NameEx("...")
    */
  val recSet = new TlaSetOper {
    override def arity: OperArity = AnyEvenArity()
    override val name: String = "$SetOfRcds"
  }

  /**
    * Construct a set of sequences from a set S i.e., Seq(S).
    */
  val seqSet = new TlaSetOper {
    override def arity: OperArity = FixedArity(1)
    override val name: String = "Seq(_)"
  }

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

  /**
    * The standard \subset operator.
    *
    * WARNING: Do not confuse with SUBSET that is implemented by TlaSetOper.powerset.
    */
  val subsetProper = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\subset"
  }

  /** the standard \supset operator */
  val supsetProper = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\supset"
  }

  /** the standard \supseteq operator */
  val supseteq = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\supseteq"
  }

  /** the standard set difference */
  val setminus = new TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\setminus"
  }

  /**
    * A restricted set comprehension: { x \in S : p }.
    * The argument order is: (x, S, p). Note that x may be a tuple.
    */
  val filter = new TlaSetOper {
    // Jure, 24.11.2017:
    // Should we unify notation with TlaFunOper.funDef? funDef has args (e, (x, S)+ )
    //
    // Igor @ 19.12.2018: What's the point? The only use of multiple parameters,
    // is to filter a Cartesian product. In this case, one can directly pass a Cartesian
    // product as an argument. The tuple gives us some form of primitive pattern matching.
    override val arity = FixedArity(3)
    override val name = "filter"
  }

  /**
    * A set mapping: { e: x_1 \in S_1, ..., x_k \in S_k }.
    * The argument order is: (e, x_1, S_1, ..., x_k, S_k)
    */
  val map = new TlaSetOper {
    override val arity = new OperArity( k => k >= 3 && k % 2 == 1 )
    override val name = "map"
  }

  /** TLA SUBSET, i.e., the set of all subsets (of a given set).
    We use the name 'powerset' to avoid confusion with \subset and \subseteq.
    */
  val powerset = new TlaSetOper {
    override val arity = FixedArity(1)
    override val name = "SUBSET"
  }

  /**
    * An alias for powerset, as TLA+ has this (rather confusing) keyword for the powerset.
    *
    * WARNING: Do not confuse with subsetProper, that is, a proper subset relation.
    */
  val SUBSET: TlaSetOper = powerset

  /** TLA UNION, i.e., the union of all elements (of a given set).

    WARNING: use it when you really need it. In all other cases, use \cup.
    */
  val union = new TlaSetOper {
    override val arity = FixedArity(1)
    override val name = "UNION"
  }

  /**
    Define a cartesian product of one or more sets.
    Note that we explicitly forbid to construct an empty set using this operator.
    To construct an empty set, use enumSet with no arguments.
    */
  val times = new TlaSetOper {
    override val arity = AnyArity()
    override val name = "\\times"
  }
}
