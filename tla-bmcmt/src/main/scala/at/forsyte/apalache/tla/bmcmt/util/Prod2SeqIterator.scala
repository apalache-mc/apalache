package at.forsyte.apalache.tla.bmcmt.util

/**
  * An iterator over the elements of a Cartesian product of two sequences. This implementation is not quite optimal,
  * as it accesses two elements by index at each iteration.
  *
  * @tparam T1 the type of the first element
  * @tparam T2 the type of the second element
  */
class Prod2SeqIterator[T1, T2](seq1: Seq[T1], seq2: Seq[T2]) extends Iterator[(T1, T2)] {
  private val intIter = new IntTupleIterator(Seq(seq1.size - 1, seq2.size - 1))

  override def hasNext: Boolean = {
    intIter.hasNext
  }

  override def next(): (T1, T2) = {
    val indices = intIter.next()
    (seq1(indices.head), seq2(indices.tail.head))
  }
}
