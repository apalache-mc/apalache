package at.forsyte.apalache.tla.lir.oper

/**
 * Set operators.
 */
abstract class TlaSetOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaSetOper {

  /**
   * Define a set by enumerating its elements: `{e_1, ..., e_k}`.
   */
  object enumSet extends TlaSetOper {
    override val arity = AnyArity()
    override val name = "SET_ENUM"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  /**
   * Construct a set of functions from a set S to a set T, that is, `[S -> T]`.
   */
  object funSet extends TlaSetOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "FUN_SET"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  /**
   * Construct a set of records, e.g., `[ f_1: S_1, ..., f_k: S_k ]`.
   * The order of the arguments is as follows: `(f_1, S_1, ..., f_k, S_k)`.
   * The field names `f_1`, ..., `f_k`` are string constants,
   * that is, `ValEx(TlaStr("..."))` and not `NameEx("...")`.
   */
  object recSet extends TlaSetOper {
    override def arity: OperArity = AnyEvenArity()

    override val name: String = "RECORD_SET"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  /**
   * Construct a set of sequences from a set S i.e., Seq(S).
   */
  object seqSet extends TlaSetOper {
    override def arity: OperArity = FixedArity(1)

    override val name: String = "Sequences!Seq"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  /**
   * Set membership: `e \in S`.
   */
  object in extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "SET_IN"
    override val precedence: (Int, Int) = (5, 5)
  }

  /**
   * Set non-membership: `e \notin S`.
   */
  object notin extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "SET_NOT_IN"
    override val precedence: (Int, Int) = (5, 5)
  }

  /**
   * Set union, that is, `S \\union T` or `S \cup T`.
   */
  object cup extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "SET_UNION2"
    override val precedence: (Int, Int) = (8, 8)
  }

  /**
   * Set intersection, that is, `S \intersect T` or `S \cap T`.
   */
  object cap extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "SET_INTERSECT"
    override val precedence: (Int, Int) = (8, 8)
  }

  /**
   * Subset-or-equals: `S \subseteq T`.
   */
  object subseteq extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "SET_SUBSET_EQ"
    override val precedence: (Int, Int) = (5, 5)
  }

  /**
   * Set difference, that is, `S \setminus T`.
   */
  object setminus extends TlaSetOper {
    override val arity = FixedArity(2)
    override val name = "SET_MINUS"
    override val precedence: (Int, Int) = (8, 8)
  }

  /**
   * A restricted set comprehension: `{ x \in S : p }`.
   * The argument order is: `(x, S, p)`. Note that x may be a tuple.
   */
  object filter extends TlaSetOper {
    override val arity = FixedArity(3)
    override val name = "SET_FILTER"
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * A set mapping: `{ e: x_1 \in S_1, ..., x_k \in S_k }`.
   * The argument order is: `(e, x_1, S_1, ..., x_k, S_k)`.
   */
  object map extends TlaSetOper {
    override val arity = new OperArity(k => k >= 3 && k % 2 == 1)
    override val name = "SET_MAP"
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
   * The set of all subsets (of a given set): `SUBSET S`.
   * We use the name 'SET_POWERSET' to avoid confusion with `SET_SUBSET_EQ`.
   */
  object powerset extends TlaSetOper {
    override val arity = FixedArity(1)
    override val name = "SET_POWERSET"
    override val precedence: (Int, Int) = (8, 8)
  }

  /**
   * The union of all elements (of a given set): `UNION S`.
   * This operator should not confused with `S \\union T`.
   */
  object union extends TlaSetOper {
    override val arity = FixedArity(1)
    override val name = "SET_UNARY_UNION"
    override val precedence: (Int, Int) = (8, 8)
  }

  /**
   * Define a cartesian product of one or more sets.
   * Note that we explicitly forbid to construct an empty set using this operator.
   * To construct an empty set, use `enumSet` with no arguments.
   */
  object times extends TlaSetOper {
    override val arity = AnyArity()
    override val name = "SET_TIMES"
    override val precedence: (Int, Int) = (10, 13)
  }
}
