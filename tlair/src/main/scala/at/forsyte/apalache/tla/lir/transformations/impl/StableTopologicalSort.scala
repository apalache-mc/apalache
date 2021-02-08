package at.forsyte.apalache.tla.lir.transformations.impl

/**
 * An implementation of a topological sort following <a href="https://en.wikipedia.org/wiki/Topological_sorting">Kahn's algorithm</a>.
 * Our sorting is stable, that is, when two graph nodes belong to the same layer, they are ordered by the original ordering.
 * (We are assuming that the input list contains no duplicates.)
 *
 * @tparam T the type of graph vertices
 * @author Igor Konnov
 */
class StableTopologicalSort[T]() {
  type Edges = Map[T, Set[T]]

  /**
   * Sort the elements of the list `unsorted` according to the dependencies that are stored in the incoming edges.
   * We are assuming that `inEdges` contain values for all elements of `unsorted`.
   *
   * @param inEdges  a set of incoming edges per every element of unsorted (may be empty)
   * @param unsorted a list of nodes
   * @return either Left(sorted) that contains the sorted nodes, or Right(nodes) that contains a subgraph with a cycle inside.
   */
  def sort(inEdges: Edges, unsorted: Seq[T]): Either[List[T], Set[T]] = {
    require(inEdges.keySet == unsorted.toSet)

    // save the unsorted order to guarantee stability
    val originalOrder = unsorted.zipWithIndex.foldLeft(Map.empty[T, Int]) { case (m, (e, i)) => m + (e -> i) }

    // Use Kahn's algorithm to sort the declarations in a topological order:
    // https://en.wikipedia.org/wiki/Topological_sorting
    //
    // In this version, we are introducing declarations layer by layer, starting with layer 0 that contains
    // the declarations that have no incoming edges, then the declarations of layer 1 that have incoming edges
    // only from layer 1, etc. Within each layer, we maintain the original order of declarations.

    // the list of sorted nodes
    var sorted = List.empty[T]
    // the edges that have not been closed in the graph yet
    var edges = inEdges
    // the list of nodes that do not have incoming edges
    var sinks = List.empty[T]

    def updateSinksAndEdges(): Unit = {
      val (sinkEdges, otherEdges) = edges.partition(_._2.isEmpty)
      // since the sinks have no incoming edges, we can sort them by the original order
      sinks = sinkEdges.keys.toList.sortWith { (l, r) =>
        originalOrder(l) < originalOrder(r)
      }
      edges = otherEdges
    }

    // initialize sinks with the nodes that have no incoming edges
    updateSinksAndEdges()
    while (sinks.nonEmpty) {
      sorted ++= sinks
      val toRemove = sinks.toSet
      // remove all incoming edges that contain one of the sinks as a source
      edges = edges.transform { (_, callers) =>
        callers -- toRemove
      }
      // recompute the sinks and edges
      updateSinksAndEdges()
    }

    if (edges.isEmpty) {
      Left(sorted)
    } else {
      Right(edges.keySet)
    }
  }
}
