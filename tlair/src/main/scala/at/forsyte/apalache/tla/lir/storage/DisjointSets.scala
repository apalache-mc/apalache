package at.forsyte.apalache.tla.lir.storage

/**
 * `DisjointSets` (DJS) manages a collection of elements, separated into equivalence classes.
 * Each equivalence class is disjoint from all the others by construction.
 * @tparam T: The type of the elements partitioned into equivalence classes
 */
trait DisjointSets[T] {

  /**
   * Returns a pair `(a,b)`, where `a` is the representative of the equivalence class that `elem` belongs to.
   * This representative is the same for all members of an equivalence class.
   * As `find` modifies the internal representation and DJS are immutable, `b` is the new state of the DJS, after
   * the internal modifications.
   * If `elem` is not a member of the collection, throws a `NoSuchElementException`.
   */
  def find(elem: T): (T, DisjointSets[T])

  /**
   * Performs the merger of the equivalence classes, to which `elem1` and `elem2` belong.
   * Returns a pair `(a,b)`, where `a` is the representative of the merged equivalence class
   * and  `b` is the new state of the DJS. If `elem1` and `elem2` belong to the same equivalence
   * class already, `merge(elem1,elem2)` is equivalent to `find(elem1)`.
   * If `elem1` or `elem2` is not a member of the collection, throws a `NoSuchElementException`.
   */
  def merge(elem1: T, elem2: T): (T, DisjointSets[T])

  /**
   * Extends the underlying collection with `elems`. For every element `e` of `elems`:
   *  - if `contains(e)`, nothing happens
   *  - otherwise, `e` is added as a singleton equivalence class
   */
  def add(elems: T*): DisjointSets[T]

  /**
   * Returns true iff `elem` is a member of some disjoint set.
   */
  def contains(elem: T): Boolean

  /**
   * Returns the number of disjoint sets partitioning the collection.
   */
  def nSets: Int

  /**
   * Returns all elements in the collection, i.e., the union of all disjoint sets.
   */
  def elems: Set[T]

  /**
   * Returns the set of representatives, i.e., one element per disjoint set.
   */
  def representatives: Set[T]
}

/**
 * Implementation of the DJS trait.
 *
 * Each set is represented as a tree, where the root node is the representative.
 * The `ranks` mapping determines, upon `merge`, how trees are combined. Specifically, when merging
 * two sets with representatives `r1` and `r2`, the representative with the lower rank among the two
 * becomes the child of the one with the higher rank. Then, the rank of the new parent becomes the sum
 * of both ranks (in this implementation, rank equals the number of nodes in the subtree).
 */
class DisjointSetsImpl[T](
    private val parents: Map[T, T], private val ranks: Map[T, DisjointSets.rankType]
) extends DisjointSets[T] {

  import DisjointSets.rankType
  private val defaultRank: rankType = 1

  /**
   * Collects all of the elements on the path up the tree from `elem` to its representative.
   * After a `find`, all of the elements on the path are rebound, so that their parent directly becomes
   * the representative. This keeps the amortized lookup time low.
   */
  private def getChain(elem: T): (T, List[T]) = {
    val parent = parents(elem)
    if (elem == parent)
      (parent, List.empty[T])
    else {
      val (repr, partialChain) = getChain(parent)
      (repr, elem :: partialChain)
    }
  }

  override def contains(elem: T): Boolean = parents.contains(elem) && ranks.contains(elem)

  override def add(elems: T*): DisjointSetsImpl[T] = {
    val newElems = elems.filterNot(contains) // just ignore all elements already tracked
    val newParents = newElems.foldLeft(parents) { case (partialPar, el) =>
      partialPar + (el -> el) // by default, each element is in a singleton, i.e., points to itself
    }
    val newRanks = newElems.foldLeft(ranks) { case (partialRnk, el) =>
      partialRnk + (el -> defaultRank)
    }
    new DisjointSetsImpl[T](newParents, newRanks)

  }

  override def find(elem: T): (T, DisjointSetsImpl[T]) = {
    if (!contains(elem))
      throw new NoSuchElementException(s"$elem is not tracked by this structure.")
    val (repr, chain) = getChain(elem)
    val newParents = chain.foldLeft(parents) { case (partialMap, el) =>
      partialMap + (el -> repr)
    }
    (repr, new DisjointSetsImpl(newParents, ranks))
  }

  override def merge(elem1: T, elem2: T): (T, DisjointSetsImpl[T]) = {
    val (repr1, postFind1) = find(elem1)
    val (repr2, postFind2) = postFind1.find(elem2)

    if (repr1 == repr2) // same EQ already
      return (repr2, postFind2)

    val r1 = ranks(elem1) // find doesn't change ranks, we can use the current map
    val r2 = ranks(elem2)

    // Higher rank becomes the parent. Tie favors repr1.
    val (newParent, newChild) = if (r1 < r2) (repr2, repr1) else (repr1, repr2)
    val newRanks = ranks + (newParent -> (r1 + r2))
    val newParents = postFind2.parents + (newChild -> newParent)

    (newParent, new DisjointSetsImpl[T](newParents, newRanks))
  }

  override def nSets: Int = representatives.size

  override def representatives: Set[T] = parents.values.toSet

  override def elems: Set[T] = parents.keySet

  def ==(other: DisjointSetsImpl[T]) = {
    this.parents == other.parents && this.ranks == other.ranks
  }
}

object DisjointSets {
  type rankType = Int

  def empty[T]: DisjointSetsImpl[T] = new DisjointSetsImpl[T](Map.empty, Map.empty)
}
