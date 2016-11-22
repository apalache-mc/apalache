package at.forsyte.apalache.tla.lir.oper

/**
 * Function operators.
 */
abstract class TlaFunOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaFunOper {
  /**
    * a function constructor like the one for the records: k_1 |-> v_1, ..., k_n |-> v_n
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
    override val name = "<...>"
  }

  /** f[e] */
  val app = new TlaFunOper {
    override val arity: OperArity = FixedArity(2)
    override val name: String = "fun-app"
  }

  /** DOMAIN f */
  val domain = new TlaFunOper {
    override val arity: OperArity = FixedArity(1)
    override val name: String = "DOMAIN"
  }

  /** [ x \in S |-> e ] */
  val funDef = new TlaFunOper {
    override def arity: OperArity = FixedArity(3)

    override def name: String = "fun-def"
  }

  /** [f EXCEPT ![i1] = e_1, ![i_2] = e_2, ..., ![i_k] = e_k] */
  val except = new TlaFunOper {
    override def arity: OperArity = AnyOddArity()

    override def name: String = "EXCEPT"
  }
}
