package at.forsyte.apalache.tla.lir.transformations.impl

import org.junit.runner.RunWith
import org.scalacheck.Prop.{falsified, forAll, passed}
import org.scalacheck.{Arbitrary, Gen, Prop}
import org.scalacheck.Prop.propBoolean
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestStableTopologicalSort extends FunSuite with BeforeAndAfterEach with Checkers {
  private def genEdges(bound: Int): Gen[List[(Int, Set[Int])]] =
    for {
      size <- Gen.choose(1, bound)
      // generate a list of numbers
      nodes <- Gen.listOfN(size, Arbitrary.arbitrary[Int])
      // generate a list of references to the names, one per position
      uses <- Gen.listOfN(size, Gen.choose(0, size - 1))
      // the declarations below the threshold do not refer to other declarations
      threshold <- Gen.choose(0, size - 1)
    } yield nodes.zip(uses).map { case (n, i) =>
      // either no dependencies or a single dependency
      if (i <= threshold) (i, Set.empty[Int]) else (i, Set(uses(i)))
    }

  // test whether the sequence of simple declarations (as above) is sorted, that is,
  // every operator applies an operator that has been defined before
  def isSorted(edges: Map[Int, Set[Int]], nodes: Seq[Int]): Prop = {
    var visited = Set.empty[Int]
    for (d <- nodes) {
      val deps = edges(d)
      if ((deps -- visited).nonEmpty) {
        return falsified
      }

      visited += d
    }
    passed
  }

  // test whether witnesses contain a cycle in the graph that is formed by edges
  def isOnCycle(edges: Map[Int, Set[Int]], witnesses: Set[Int]): Prop = {
    // Use simple breadth-first search for testing purposes
    var visited = Set.empty[Int]
    var front = witnesses
    while (front.nonEmpty) {
      visited = visited ++ front
      front = front.foldLeft(Set.empty[Int]) { case (s, i) => s ++ edges(i) }
      if (front.intersect(witnesses).nonEmpty) {
        return passed
      }
      front = front -- visited
    }
    falsified
  }

  // stability is a bit hard to specify, so we only do it for level 0, that is, the nodes without incoming edges
  def isStableLayer0(edges: Map[Int, Set[Int]], unsorted: Seq[Int], sorted: Seq[Int]): Prop = {
    val layer0 = edges.filter(_._2.isEmpty).keySet
    // since nodes in layer0 have no dependencies, they have to be sorted according to unsorted
    val unsorted0 = unsorted.filter(layer0.contains)
    val sorted0 = sorted.filter(layer0.contains)
    // pretty cool, right?
    if (unsorted0 == sorted0) {
      passed
    } else {
      falsified
    }
  }

  // shrinking does not help us here

  import org.scalacheck.Shrink.shrinkAny

  test("either sort a random sequence or give us a witness of a cycle") {
    def sortOrFail: Prop = {
      forAll(genEdges(10)) { edges =>
        val unsorted = edges.map(_._1)
        val edgesMap = edges.toMap
        val result = new StableTopologicalSort[Int].toposort(edgesMap, unsorted)
        result match {
          case Left(sorted) =>
            isSorted(edgesMap, sorted) :| ("sorted: " + sorted) &&
              ((unsorted.distinct == unsorted) ==>
                isStableLayer0(edgesMap, unsorted, sorted) :| ("sorted: " + sorted))

          case Right(witnesses) =>
            isOnCycle(edgesMap, witnesses) :| ("witnesses: " + witnesses)
        }
      }
    }

    check(sortOrFail, minSuccessful(10000))
  }
}
