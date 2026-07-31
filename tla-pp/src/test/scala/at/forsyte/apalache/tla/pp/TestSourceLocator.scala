package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.aux._
import at.forsyte.apalache.tla.lir.src.{SourceLocation, SourcePosition, SourceRegion}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator, SourceMap}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker, decorateWithPrime}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSourceLocator extends AnyFunSuite {
  private val intToInt = OperT1(Seq(IntT1), IntT1)
  private val intIntToInt = OperT1(Seq(IntT1, IntT1), IntT1)
  private val higherOrderToInt = OperT1(Seq(intToInt, IntT1), IntT1)
  private val nullaryInt = OperT1(Seq.empty, IntT1)

  // plus(a, b) == a + b
  private val plusDecl: TlaOperDecl =
    tla
      .decl(
        "plus",
        tla.plus(tla.name("a", IntT1), tla.name("b", IntT1)),
        tla.param("a", IntT1),
        tla.param("b", IntT1),
      )
      .build

  // App(X(_), p) == X(p)
  private val applyDecl: TlaOperDecl =
    tla
      .decl(
        "App",
        tla.appOp(tla.name("X", intToInt), tla.name("p", IntT1)),
        tla.param("X", intToInt),
        tla.param("p", IntT1),
      )
      .build

  private val declarations = List(
    plusDecl,
    applyDecl,
  )

  // x' /\ y
  private val primedConjunction =
    tla.and(tla.prime(tla.name("x", BoolT1)), tla.name("y", BoolT1)).build
  // LET A(p) == p + 1 IN
  // A(1) >= 0
  private val localApplication =
    tla
      .letIn(
        tla.ge(tla.appOp(tla.name("A", intToInt), tla.int(1)), tla.int(0)),
        tla.decl("A", tla.plus(tla.name("p", IntT1), tla.int(1)), tla.param("p", IntT1)),
      )
      .build
  // plus(x, 1)
  private val topLevelApplication =
    tla.appOp(tla.name("plus", intIntToInt), tla.name("x", IntT1), tla.int(1)).build
  // LET I(p) == p IN
  // IF y THEN App(I, 0) ELSE 1
  private val higherOrderApplication =
    tla
      .letIn(
        tla.ite(
          tla.name("y", BoolT1),
          tla.appOp(tla.name("App", higherOrderToInt), tla.name("I", intToInt), tla.int(0)),
          tla.int(1),
        ),
        tla.decl("I", tla.name("p", IntT1), tla.param("p", IntT1)),
      )
      .build
  // LET A(p, q) == IntentionallyUndefinedOper(p, q) IN
  //   LET B == b
  //       C(p) == A(p, B())
  //   IN
  //   LET D == x IN
  //   C(D())
  private val nestedLetIn =
    tla
      .letIn(
        tla.letIn(
          tla.letIn(
            tla.appOp(tla.name("C", intToInt), tla.appOp(tla.name("D", nullaryInt))),
            tla.decl("D", tla.name("x", IntT1)),
          ),
          tla.decl("B", tla.name("b", IntT1)),
          tla.decl(
            "C",
            tla.appOp(
              tla.name("A", intIntToInt),
              tla.name("p", IntT1),
              tla.appOp(tla.name("B", nullaryInt)),
            ),
            tla.param("p", IntT1),
          ),
        ),
        tla.decl(
          "A",
          tla.appOp(
            tla.name("IntentionallyUndefinedOper", intIntToInt),
            tla.name("p", IntT1),
            tla.name("q", IntT1),
          ),
          tla.param("p", IntT1),
          tla.param("q", IntT1),
        ),
      )
      .build
  // UNCHANGED x
  private val unchangedName = tla.unchanged(tla.name("x", IntT1)).build
  // UNCHANGED <<x, y>>
  private val unchangedTuple =
    tla.unchanged(tla.tuple(tla.name("x", IntT1), tla.name("y", IntT1))).build
  // [x |-> 1].x
  private val recordAccess = tla.app(tla.rec("x" -> tla.int(1)), tla.str("x")).build

  private val expressions = List(
    primedConjunction,
    localApplication,
    topLevelApplication,
    higherOrderApplication,
    nestedLetIn,
    unchangedName,
    unchangedTuple,
    recordAccess,
  )

  private def generateLocation(uid: UID) =
    new SourceLocation(
        "filename",
      SourceRegion(
        SourcePosition(uid.id.toInt / 1000, uid.id.toInt % 1000),
        SourcePosition(uid.id.toInt / 1000, uid.id.toInt % 1000),
        ),
    )

  // Arbitrary assignment: every source expression gets a unique position derived from its UID.
  private val sourceMap: SourceMap =
    (expressions.flatMap(allUidsBelow) ++ declarations.flatMap(d => allUidsBelow(d.body)))
      .map(uid => uid -> generateLocation(uid))
      .toMap

  private def assertLocationsPreserved(makeTransformation: TransformationTracker => TlaExTransformation): Unit = {
    val changeListener = new ChangeListener
    val tracker = TrackerWithListeners(changeListener)
    val locator = SourceLocator(sourceMap, changeListener)
    val transform = makeTransformation(tracker)
    val transformedIds = expressions.flatMap(ex => allUidsBelow(transform(ex))).toSet

    val missingLocations = transformedIds.filter(uid => locator.sourceOf(uid).isEmpty)
    assert(missingLocations.isEmpty, s"Missing source locations for: ${missingLocations.mkString(", ")}")
  }

  test("Test DeepCopy") {
    assertLocationsPreserved(tracker => DeepCopy(tracker).deepCopyEx[TlaEx] _)
  }

  test("Test Flatten") {
    assertLocationsPreserved(tracker => Flatten(tracker)(Untyped))
  }

  test("Test IncrementalRenaming") {
    assertLocationsPreserved(tracker => new IncrementalRenaming(tracker))
  }

  test("Test Inline") {
    assertLocationsPreserved { tracker =>
      new Inliner(tracker, new IncrementalRenaming(tracker)).transformEx
    }
  }

  test("Test NoOp") {
    assertLocationsPreserved(_.trackEx { case ex => ex })
  }

  test("Test Prime") {
    assertLocationsPreserved(tracker => decorateWithPrime(Set("x", "y"), tracker))
  }
}
