package at.forsyte.apalache.tla.lir.storage

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDisjointSets extends FunSuite {

  test("bad calls") {
    val djs = DisjointSets.empty[Int].add(1, 2, 3)
    assertThrows[NoSuchElementException] {
      djs.find(0)
    }
    assertThrows[NoSuchElementException] {
      djs.merge(0, 1)
    }
    assertThrows[NoSuchElementException] {
      djs.merge(1, 0)
    }
  }

  test("add") {
    val djs = DisjointSets.empty[Int]
    assert(djs.nSets == 0)
    val elems = Seq(1, 2, 3, 1, 2, 3)
    val elemsSet = elems.toSet
    val newDjs = djs.add(elems: _*)
    assert(newDjs.nSets == elemsSet.size)
    assert(newDjs.elems == elemsSet)
  }

  test("find(x) = x") {
    val djs = DisjointSets.empty[Int].add(1, 2, 3)
    djs.elems.foreach { el =>
      assert(djs.find(el)._1 == el)
    }
  }

  test("merge") {
    val djs: DisjointSetsImpl[Int] = DisjointSets.empty.add(1, 2, 3, 4)

    val (repr1, sameDjs) = djs.merge(1, 1)
    assert(sameDjs == djs && repr1 == 1)

    val (_, newDjs) = djs.merge(1, 3)
    assert(djs.nSets == newDjs.nSets + 1)
    assert(newDjs.find(1)._1 == newDjs.find(3)._1)
  }

  test("dummy merge = find") {
    val djs: DisjointSetsImpl[Int] = DisjointSets.empty.add(1, 2, 3, 4)
    val (_, merge23) = djs.merge(2, 3)
    val (_, merge12) = merge23.merge(1, 2)

    val dummyMergePair = merge12.merge(1, 1)
    val findPair = merge12.find(1)

    assert(dummyMergePair._1 == findPair._1)
    assert(dummyMergePair._2 == findPair._2)
  }

  test("mergeAll") {
    val djs = DisjointSets.empty[Int].add(1, 2, 3, 4)
    val newDjs = djs.elems.foldLeft(djs) { case (partialDjs, el) =>
      partialDjs.merge(1, el)._2
    }
    assert(newDjs.nSets == 1)
  }

}
