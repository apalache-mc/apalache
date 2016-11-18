package at.forsyte.apalache.tla.lir.oper

/**
  * Created by jkukovec on 11/17/16.
  */

abstract class TlaSeqOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaSeqOper {

  /**
  Define a sequence by listing its elements, i.e., < e_1, ..., e_k >
    */
  val enumSeq = new TlaSeqOper {
    override val arity = AnyArity()
    override val name = "<...>"
  }

  val head = new TlaSeqOper {
    override val arity = FixedArity(1)
    override val name = "Head(_)"
  }

  val tail = new TlaSeqOper {
    override val arity = FixedArity(1)
    override val name = "Tail(_)"
  }

  val append = new TlaSeqOper {
    override val arity = FixedArity(2)
    override val name = "Append(_,_)"
  }

  val concat = new TlaSeqOper {
    override val arity = FixedArity(1)
    override val name = "_o_"
  }

  val len = new TlaSeqOper {
    override val arity = FixedArity(1)
    override val name = "Len(_)"
  }
}
