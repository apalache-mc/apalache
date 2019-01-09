package at.forsyte.apalache.tla.imp.src

/**
  * A tree that stores source regions in the order of their nesting. We assume that a region can be included into
  * another, but otherwise regions cannot intersect. Every region in the tree is assigned a unique index that can be
  * used to access the region.
  *
  * @author Igor Konnov
  */
class RegionTree {
  private class Node(val index: Int, val region: SourceRegion, val children: Seq[Node])

  private val rootRegion = SourceRegion(SourcePosition(0), SourcePosition(Int.MaxValue))
  private var root: Node = new Node(0, rootRegion, Seq())
  private var regions: Seq[SourceRegion] = Seq(rootRegion)

  /**
    * Add a region in the tree. If the tree contains an overlapping region that does not include the given region,
    * an IllegalArgumentException is thrown.
    * @param region a region to add
    * @return the index of the added region
    */
  def add(region: SourceRegion): Int = {
    var newIndex: Int = -1

    def locateAndAdd(node: Node): Node = {
      if (region.isInside(node.region)) {
        // the new region should be added as a child, either of the node, or of one of its children
        if (node.children.exists(_.region.contains(region))) {
          // add the region as a child of one of the children
          new Node(node.index, node.region, node.children map locateAndAdd)
        } else if (node.children.exists(n => n.region.isIntersecting(region) && !n.region.isInside(region))) {
          // this is a problem
          val conflict = node.children.find(_.region.isIntersecting(region)).get
          throw new IllegalArgumentException("The argument region %s intersects with %s".format(region, conflict.region))
        } else {
          if (region != node.region) {
            newIndex = regions.size // assign a new index
            regions :+= region      // add to the tail
            // the new region may cover the previously added children
            val (childsChildren, parentsChildren) = node.children.partition(_.region.isInside(region))
            new Node(node.index, node.region, new Node(newIndex, region, childsChildren) +: parentsChildren)
          } else {
            newIndex = node.index
            node
          }
        }
      } else if (region.isIntersecting(node.region)) {
        // this should not be possible due to the check above
        throw new IllegalArgumentException("The argument region %s intersects with %s".format(region, node.region))
      } else {
        // do nothing
        node
      }
    }
    root = locateAndAdd(root)
    assert(newIndex > 0)
    newIndex
  }

  /**
    * Find a region by an index. If there is no such a region, throw IndexOutOfBoundsException.
    * @param index an index that was returned by add
    * @return the region that has the given index
    */
  def apply(index: Int): SourceRegion = {
    regions(index) // as we are adding children to the head, not the tail
  }

  /**
    * Return the number of regions in the tree.
    * @return the number of regions
    */
  def size: Int = {
    regions.size - 1 // not counting the root region
  }
}
