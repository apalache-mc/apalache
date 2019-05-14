package at.forsyte.apalache.tla.lir.oper

/**
  * Sequence operators
  *
  * @author Jure Kukovec
  *
  * Created by jkukovec on 11/17/16.
  */

abstract class TlaSeqOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

/**
  * The standard module of Sequences. Note that there is no standard constructor for a sequence.
  * Use the tuples constructor, @see TlaOper.
  */
object TlaSeqOper {

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
    override val arity = FixedArity(2)
    override val name = "_o_"
  }

  val len = new TlaSeqOper {
    override val arity = FixedArity(1)
    override val name = "Len(_)"
  }

  val subseq = new TlaSeqOper {
    override val arity = FixedArity(3)
    override val name = "SubSeq(_, _, _)"
  }

  val selectseq = new TlaSeqOper {
    override val arity = FixedArity(2)
    override val name = "SelectSeq(_, _)"
  }
}
