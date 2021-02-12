package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestIncrementalRenaming extends FunSuite with TestingPredefs with BeforeAndAfterEach {

  import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming._
  import Builder._

  private var renaming = new IncrementalRenaming(TrackerWithListeners())

  override protected def beforeEach(): Unit = {
    renaming = new IncrementalRenaming(TrackerWithListeners())
  }

  test("Test parseName") {
    val initialName = "name"
    val renamed = makeName(initialName, 42)
    val invalid = makeName(renamed, 2)

    assert(parseName(initialName).isEmpty)
    assert(parseName(renamed).contains((initialName, 42)))
    assertThrows[IllegalArgumentException] {
      parseName(invalid)
    }
  }

  test("Test mergeNameCounters") {
    val m1 = Map("x" -> 1)
    val m2 = Map("x" -> 2)
    val m3 = Map("y" -> 2)
    val m4 = Map("x" -> 99, "y" -> 99)

    val mergeMax = mergeNameCounters(takeMax = true)(_, _)
    val mergeMin = mergeNameCounters(takeMax = false)(_, _)

    assert(mergeMax(Map.empty, Map.empty).isEmpty)
    assert(mergeMax(Map.empty, m1) == m1)
    assert(mergeMax(m1, Map.empty) == m1)
    assert(mergeMax(m1, m2) == m2)
    assert(mergeMax(m2, m1) == m2)
    assert(mergeMax(m2, m3) == Map("x" -> 2, "y" -> 2))
    assert(mergeMax(m3, m2) == Map("x" -> 2, "y" -> 2))
    assert(List(m1, m2, m3, m4).foldLeft(Map.empty[String, Int]) {
      mergeMax
    } == m4)
    assert(List(m4, m2, m3, m1).foldLeft(Map.empty[String, Int]) {
      mergeMax
    } == m4)

    assert(mergeMin(Map.empty, Map.empty).isEmpty)
    assert(mergeMin(Map.empty, m1) == m1)
    assert(mergeMin(m1, Map.empty) == m1)
    assert(mergeMin(m1, m2) == m1)
    assert(mergeMin(m2, m1) == m1)
    assert(mergeMin(m2, m3) == Map("x" -> 2, "y" -> 2))
    assert(mergeMin(m3, m2) == Map("x" -> 2, "y" -> 2))
    assert(List(m1, m2, m3, m4).foldLeft(Map.empty[String, Int]) {
      mergeMin
    } == Map("x" -> 1, "y" -> 2))
    assert(List(m4, m2, m3, m1).foldLeft(Map.empty[String, Int]) {
      mergeMin
    } == Map("x" -> 1, "y" -> 2))
  }

  test("Test nameCounterMapFromEx [TlaEx]") {
    val ex = and(n_x, n_y, n_z, eql(plus(n_t, n_z), int(2)))

    assert(nameCounterMapFromEx(takeMax = true)(ex).isEmpty)

    val ex2 = and(
        name(makeName("x", 2)),
        name(makeName("y", 8)),
        n_z,
        eql(
            plus(
                name(makeName("x", 1)),
                prime(name(makeName("z", 3)))
            ),
            int(2)
        ),
        prime(n_x),
        name(makeName("x", 2))
    )

    val ex2Map = nameCounterMapFromEx(takeMax = true)(ex2)
    assert(
        ex2Map ==
          Map(
              "x" -> 2,
              "y" -> 8,
              "z" -> 3
          ))
  }

  test("Test nameCounterMapFromEx [LET-IN TlaDecl]") {
    val p1Name = makeName("p", 1)
    val p3Name = makeName("p", 3)
    val p8Name = makeName("p", 8)
    val s3Name = makeName("s", 3)
    val s5Name = makeName("s", 5)

    val xDecl =
      declOp(
          "X",
          and(
              ge(
                  name(p1Name),
                  int(0)
              ),
              primeInSingleton(n_x, name(p1Name))
          ),
          p1Name,
          (makeName("t", 99), 2) //unused
      )

    val yDecl =
      declOp(
          makeName("Y", 6),
          exists(
              name(s3Name),
              name(makeName("T", 1)),
              eql(
                  plus(
                      name(s3Name),
                      name(p3Name)
                  ),
                  n_x
              )
          ),
          p3Name
      )

    val zDecl =
      declOp(
          makeName("Z", 1),
          name(p8Name),
          p8Name
      )

    /**
     * LET X(p1,t99(_,_)) == /\ p1 >= 0
     * /\ x' \in {p1}
     * Z1(p8) == p8
     * IN LET Y6(p3) == \E s3 \in T1 : s3 + p3 = x
     * IN /\ \A s5 \in T1 : /\ Z1(s5)
     * /\ Y6(s5)
     * /\ y
     * /\ X(0,x)
     */
    val letInEx =
      letIn(
          letIn(
              and(
                  forall(
                      name(s5Name),
                      name(makeName("T", 1)),
                      and(
                          appDecl(zDecl, name(s5Name)),
                          appDecl(yDecl, name(s5Name))
                      )
                  ),
                  n_y,
                  appDecl(xDecl, int(0), n_x)
              ),
              yDecl
          ),
          xDecl,
          zDecl
      )

    val letInExMap = nameCounterMapFromEx(takeMax = true)(letInEx)
    assert(
        letInExMap ==
          Map(
              "p" -> 8,
              "s" -> 5,
              "T" -> 1,
              "Y" -> 6,
              "Z" -> 1,
              "t" -> 99
          ))

  }

  test("Test apply: basic") {
    val ex1 = n_x
    val renamed1 = renaming(ex1)

    assert(ex1 == renamed1)

    val ex2 = exists(n_s, n_T, n_s)
    val renamed2 = renaming(ex2)
    assert(renamed2 == exists(name(makeName("s", 1)), n_T, name(makeName("s", 1))))

    val renamed2again = renaming(renamed2)
    assert(renamed2again == exists(name(makeName("s", 2)), n_T, name(makeName("s", 2))))

  }

  test("Test apply: exists/forall") {
    val original =
      and(exists(n_x, n_S, gt(n_x, int(1))), forall(n_x, n_T, lt(n_x, int(42))))

    def expected(offset: Int): TlaEx =
      and(
          exists(name(makeName("x", offset + 1)), n_S, gt(name(makeName("x", offset + 1)), int(1))),
          forall(name(makeName("x", offset + 2)), n_T, lt(name(makeName("x", offset + 2)), int(42)))
      )

    val renamed = renaming(original)
    assert(renamed == expected(0))

    val renamedTwice = renaming(renamed)
    assert(renamedTwice == expected(2))

  }

  test("Test apply: filter") {
    val original =
      cup(
          filter(n_x, n_S, eql(n_x, int(1))),
          filter(n_x, n_S, eql(n_x, int(2)))
      )
    val x1 = makeName("x", 1)
    val x2 = makeName("x", 2)

    def expected(offset: Int): TlaEx =
      cup(
          filter(name(makeName("x", offset + 1)), n_S, eql(name(makeName("x", offset + 1)), int(1))),
          filter(name(makeName("x", offset + 2)), n_S, eql(name(makeName("x", offset + 2)), int(2)))
      )

    val renamed = renaming(original)
    assert(renamed == expected(0))

    val renamedTwice = renaming(renamed)
    assert(renamedTwice == expected(2))
  }

  test("Test apply: LET-IN") {
    // LET p(t) == \A x \in S . R(t,x) IN \E x \in S . p(x)
    val original =
      letIn(
          exists(n_x, n_S, appOp(name("p"), n_x)),
          declOp("p", forall(n_x, n_S, appOp(name("R"), name("t"), n_x)), "t")
      )

    val expected =
      letIn(
          exists(name(makeName("x", 2)), n_S, appOp(name(makeName("p", 1)), name(makeName("x", 2)))),
          declOp(makeName("p", 1),
              forall(name(makeName("x", 1)), n_S, appOp(name("R"), name(makeName("t", 1)), name(makeName("x", 1)))),
              makeName("t", 1))
      )

    val actual = renaming(original)

    assert(expected == actual)

    val renamedTwice = renaming(actual)

    val expected2 =
      letIn(
          exists(name(makeName("x", 4)), n_S, appOp(name(makeName("p", 2)), name(makeName("x", 4)))),
          declOp(makeName("p", 2),
              forall(name(makeName("x", 3)), n_S, appOp(name("R"), name(makeName("t", 2)), name(makeName("x", 3)))),
              makeName("t", 2))
      )

    assert(renamedTwice == expected2)
  }

  test("Test apply: multiple LET-IN") {
    // LET X == TRUE IN X /\ LET X == FALSE IN X
    val original =
      and(
          letIn(
              appOp(name("X")),
              declOp("X", trueEx)
          ),
          letIn(
              appOp(name("X")),
              declOp("X", falseEx)
          )
      )

    def expected(offset: Int) =
      and(
          letIn(
              appOp(name(makeName("X", offset + 1))),
              declOp(makeName("X", offset + 1), trueEx)
          ),
          letIn(
              appOp(name(makeName("X", offset + 2))),
              declOp(makeName("X", offset + 2), falseEx)
          )
      )

    val renamed = renaming(original)

    assert(renamed == expected(0))

    val renamedTwice = renaming(renamed)

    assert(renamedTwice == expected(2))
  }

  test("Test offsetName") {
    val offsets = Map(
        "x" -> 1
    )

    val fn: String => String = offsetName(offsets)

    val name1 = "x"
    val expected1 = "x"
    val actual1 = fn(name1)
    assert(expected1 == actual1)

    val name2 = makeName("x", 1)
    assertThrows[AssertionError] {
      fn(name2)
    }

    val name3 = makeName("x", 2)
    val expected3 = makeName("x", 1)
    val actual3 = fn(name3)
    assert(expected3 == actual3)

    val name4 = makeName("y", 2)
    val expected4 = makeName("y", 2)
    val actual4 = fn(name4)
    assert(expected4 == actual4)

  }

  test("Test shiftCounters") {
    val offsets = Map(
        "x" -> 4,
        "y" -> 2,
        "z" -> 3
    )

    val ex = gt(
        plus(
            name(makeName("x", 5)),
            name(makeName("y", 3))
        ),
        name(makeName("z", 4))
    )

    val expected = gt(
        plus(
            name(makeName("x", 1)),
            name(makeName("y", 1))
        ),
        name(makeName("z", 1))
    )

    val actual = renaming.shiftCounters(offsets)(ex)
    assert(expected == actual)
  }

  test("Test normalize") {
    val ex = gt(
        plus(
            name(makeName("x", 5)),
            name(makeName("y", 3))
        ),
        name(makeName("z", 4))
    )

    val expected = gt(
        plus(
            name(makeName("x", 1)),
            name(makeName("y", 1))
        ),
        name(makeName("z", 1))
    )

    val actual = renaming.normalize(ex)
    assert(expected == actual)
  }

  test("Test syncFrom") {
    val ex = exists(name(makeName("x", 5)), n_S, n_p)

    val expected = exists(name(makeName("x", 6)), n_S, n_p)

    renaming.syncFrom(ex)
    val actual = renaming(ex)
    assert(expected == actual)
  }

  test("Test syncAndNormalizeDs") {
    val syncEx = exists(name(makeName("x", 99)), n_S, n_p)
    renaming.syncFrom(syncEx) // Set x -> 99 in the map

    val ex1 = exists(name(makeName("x", 3)), n_S, n_p)
    val ex2 = exists(name(makeName("x", 105)), n_S, n_p)

    val xDecl = declOp("X", ex1)
    val yDecl = declOp("Y", ex2)

    val decls = Seq(xDecl, yDecl)
    val expected = Seq(
        declOp("X", exists(name(makeName("x", 1)), n_S, n_p)),
        declOp("Y", exists(name(makeName("x", 2)), n_S, n_p))
    )

    val actual = renaming.syncAndNormalizeDs(decls)

    assert(expected == actual)

  }

}
