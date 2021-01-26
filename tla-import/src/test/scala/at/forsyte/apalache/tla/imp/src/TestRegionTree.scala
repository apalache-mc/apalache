package at.forsyte.apalache.tla.imp.src

import at.forsyte.apalache.tla.lir.src.{
  RegionTree,
  SourcePosition,
  SourceRegion
}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestRegionTree extends FunSuite {
  test("add") {
    val tree = new RegionTree()
    val region = SourceRegion(SourcePosition(1, 20), SourcePosition(3, 10))
    tree.add(region)
  }

  test("add a subregion, then size") {
    val tree = new RegionTree()
    val reg1 = SourceRegion(SourcePosition(1, 20), SourcePosition(3, 10))
    tree.add(reg1)
    assert(tree.size == 1)
    val reg2 = SourceRegion(SourcePosition(1, 20), SourcePosition(2, 5))
    tree.add(reg2)
    assert(tree.size == 2)
    val reg3 = SourceRegion(SourcePosition(2, 10), SourcePosition(3, 10))
    tree.add(reg3)
    assert(tree.size == 3)
  }

  test("add an overlapping subregion") {
    val tree = new RegionTree()
    val reg1 = SourceRegion(SourcePosition(1, 10), SourcePosition(3, 10))
    tree.add(reg1)
    val reg2 = SourceRegion(SourcePosition(1, 20), SourcePosition(5, 20))
    assertThrows[IllegalArgumentException] {
      tree.add(reg2)
    }
  }

  test("add a small region, then a larger region") {
    val tree = new RegionTree()
    val reg1 = SourceRegion(SourcePosition(2, 10), SourcePosition(3, 10))
    tree.add(reg1)
    val reg2 = SourceRegion(SourcePosition(1, 1), SourcePosition(4, 1))
    tree.add(reg2)
  }

  test("add a region twice") {
    val tree = new RegionTree()
    val reg1 = SourceRegion(SourcePosition(2, 10), SourcePosition(3, 10))
    tree.add(reg1)
    val reg2 = SourceRegion(SourcePosition(2, 10), SourcePosition(3, 10))
    tree.add(reg2)
  }

  test("add and find") {
    val tree = new RegionTree()
    val region = SourceRegion(SourcePosition(1, 20), SourcePosition(3, 10))
    val idx = tree.add(region)
    val found = tree(idx)
    assert(found == region)
  }

  test("find non-existing index") {
    val tree = new RegionTree()
    val region = SourceRegion(SourcePosition(1, 20), SourcePosition(3, 10))
    val idx = tree.add(region)
    assertThrows[IndexOutOfBoundsException] {
      tree(999)
    }
  }
}
