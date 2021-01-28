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
  object enumSet extends TlaSetOper {
    override val arity = AnyArity() // FIX: we allow zero arguments as well
    override val name = "{...}"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  /**
    * Construct a set of functions from a set S to a set T, i.e., [S -> T].
    */
  object funSet extends TlaSetOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "[S -> T]"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  /**
    * Construct a set of records, e.g., [ f_1: S_1, ..., f_k: S_k ].
    * The order of the arguments is as follows: (f_1, S_1, ..., f_k, S_k).
    * The field names f_1, ..., f_k are string constants,
    * that is, ValEx(TlaStr("...")) and not NameEx("...")
    */
  object recSet extends TlaSetOper {
    override def arity: OperArity = AnyEvenArity()
    override val name: String = "$SetOfRcds"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  /**
    * Construct a set of sequences from a set S i.e., Seq(S).
    */
  object seqSet extends TlaSetOper {
    override def arity: OperArity = FixedArity(1)
    override val name: String = "Seq"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  object in extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\in"
    override val precedence: (Int, Int) = (5, 5)
  }

  object notin extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\notin"
    override val precedence: (Int, Int) = (5, 5)
  }

  object cup extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\union"
    override val precedence: (Int, Int) = (8, 8)
  }

  object cap extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\intersect"
    override val precedence: (Int, Int) = (8, 8)
  }

  /** the standard \subseteq operator */
  object subseteq extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\subseteq"
    override val precedence: (Int, Int) = (5, 5)
  }

  /**
    * The standard \subset operator.
    *
    * WARNING: Do not confuse with SUBSET that is implemented by TlaSetOper.powerset.
    */
  object subsetProper extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\subset"
    override val precedence: (Int, Int) = (5, 5)
  }

  object supsetProper extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\supset"
    override val precedence: (Int, Int) = (5, 5)
  }

  /** the standard \supseteq operator */
  object supseteq extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\supseteq"
    override val precedence: (Int, Int) = (5, 5)
  }

  /** the standard set difference */
  object setminus extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "\\setminus"
    override val precedence: (Int, Int) = (8, 8)
  }

  /**
    * A restricted set comprehension: { x \in S : p }.
    * The argument order is: (x, S, p). Note that x may be a tuple.
    */
  object filter extends TlaSetOper {
    // Jure, 24.11.2017:
    // Should we unify notation with TlaFunOper.funDef? funDef has args (e, (x, S)+ )
    //
    // Igor @ 19.12.2018: What's the point? The only use of multiple parameters,
    // is to filter a Cartesian product. In this case, one can directly pass a Cartesian
    // product as an argument. The tuple gives us some form of primitive pattern matching.
    override val arity = FixedArity(3)
    override val name = "filter"
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
    * A set mapping: { e: x_1 \in S_1, ..., x_k \in S_k }.
    * The argument order is: (e, x_1, S_1, ..., x_k, S_k)
    */
  object map extends TlaSetOper {
    override val arity = new OperArity( k => k >= 3 && k % 2 == 1 )
    override val name = "map"
    override val precedence: (Int, Int) = (16, 16)
  }

  /** TLA SUBSET, i.e., the set of all subsets (of a given set).
    We use the name 'powerset' to avoid confusion with \subset and \subseteq.
    */
  object powerset extends TlaSetOper {
    override val arity = FixedArity(1)
    override val name = "SUBSET"
    override val precedence: (Int, Int) = (8, 8)
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
  object union extends TlaSetOper {
    override val arity = FixedArity(1)
    override val name = "UNION"
    override val precedence: (Int, Int) = (8, 8)
  }

  /**
    Define a cartesian product of one or more sets.
    Note that we explicitly forbid to construct an empty set using this operator.
    To construct an empty set, use enumSet with no arguments.
    */
  object times extends TlaSetOper {
    override val arity = AnyArity()
    override val name = "\\times"
    override val precedence: (Int, Int) = (10, 13)
  }
}
