package at.forsyte.apalache.tla.lir.oper

import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
 * Function operators.
 */
abstract class TlaFunOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaFunOper {
  /**
    * A function constructor like the one for the records: [ k_1 |-> v_1, ..., k_n |-> v_n ].
    * The order of the arguments is: (k_1, v_1, ..., k_n, v_n).
    * Note that in case of records, k_1, ..., k_n are strings, that is, ValEx(TlaStr(...)), not NameEx.
    */
  val enum = new TlaFunOper {
    override def arity: OperArity = AnyEvenArity()
    override def name: String = "fun-enum"
  }

  /**
    Define a tuple by listing its elements, i.e., < e_1, ..., e_k >.
    One can use enum to achieve the same effect.
    */
  val tuple = new TlaFunOper {
    override val arity = AnyArity()
    override val name = "<<...>>"
  }

  /**
    * A short-hand constructor for tuples.
    *
    * @param elems tuple elements
    * @return a new OperEx(tuple, elems: _*)
    */
  def mkTuple(elems: TlaEx*): OperEx =
    OperEx(tuple, elems: _*)

  /**
    * A function application, e.g., f[e].
    * The order of the arguments is: (f, e).
    */
  val app = new TlaFunOper {
    override val arity: OperArity = FixedArity(2)
    override val name: String = "fun-app"
  }

  /** DOMAIN f */
  val domain = new TlaFunOper {
    override val arity: OperArity = FixedArity(1)
    override val name: String = "DOMAIN"
  }

  /**
    * A function constructor: [ x \in S |-> e ]. In fact, it is a lambda function (NOT the TLA+ LAMBDA!)
    * Similar to \E and \A, one can use many combinations of variables and tuples, e.g.,
    * [ x, y \in S, <<a, b>> \in S |-> e ]. We translate function constructors
    * in a list of fixed structure, where the defining expression comes first and every variables (or a tuple)
    * comes with its bounding set, e.g., (e, x, S, y, S, <<a, b>>, S).
    *
    * The arguments are always an odd-length list
    * of the following structure: body, x_1, R_1, ..., x_k, R_k.
    */
  val funDef = new TlaFunOper {
    override def arity: OperArity = AnyOddArity()

    override def name: String = "fun-def"
  }

  /**
    * A function update, e.g., [f EXCEPT ![i_1] = e_1, ![i_2] = e_2, ..., ![i_k] = e_k].
    * The order of the arguments is as follows: (f, i_1, e_1, ..., i_k, e_k).
    */
  val except = new TlaFunOper {
    override def arity: OperArity = AnyOddArity()

    override def name: String = "EXCEPT"
  }
}
