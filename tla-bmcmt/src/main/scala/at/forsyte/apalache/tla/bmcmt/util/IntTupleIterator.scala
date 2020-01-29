package at.forsyte.apalache.tla.bmcmt.util

import at.forsyte.apalache.tla.bmcmt.{Limits, RewriterException}
import at.forsyte.apalache.tla.lir.NullEx

/**
  * Iterate over all k-tuples from (0,...,0) up to (n_1, ..., n_k), including the tuple (n_1, ..., n_k).
  * This iterator is useful to construct Cartesian products that are needed by multiple argument operators.
  *
  * @author Igor Konnov
  */
class IntTupleIterator(limits: Seq[Int]) extends Iterator[Seq[Int]] {
  private var vec: Array[Int] = (-1) +: Array.fill(limits.size - 1)(0)
  // we have to enumerate that many elements
  private var toEnumerate: BigInt = limits.map(BigInt(_) + 1).product // bugfix: use BigInt to avoid overflow

  override def hasNext: Boolean = {
    toEnumerate > 0
  }

  override def next(): Seq[Int] = {
    if (!hasNext) {
      throw new NoSuchElementException("All elements have been enumerated")
    }
    if (toEnumerate > Limits.MAX_PRODUCT_SIZE) {
      throw new RewriterException("Too many elements to enumerate: " + toEnumerate, NullEx)
    }

    toEnumerate -= 1
    // find the first element that can be increased, i.e., it is below the limit
    def isBelowLimit(value: Int, limit: Int) = value < limit
    val index = vec.zip(limits) indexWhere (isBelowLimit _).tupled
    // all the preceding elements shift over from their limit to zero
    0.until(index).foreach(vec.update(_, 0))
    // the element at index is increased
    vec.update(index, 1+ vec(index))
    vec.toSeq
  }
}
