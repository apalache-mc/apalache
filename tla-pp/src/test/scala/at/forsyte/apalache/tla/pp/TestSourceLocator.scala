package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.aux._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.src.{SourceLocation, SourcePosition, SourceRegion}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator, SourceMap}
import at.forsyte.apalache.tla.lir.transformations.impl.{IdleTracker, TrackerWithListeners}
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.{decorateWithPrime, TlaExTransformation, TransformationListener}
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import scala.collection.mutable

// TODO: Igor, 27.08.2021: this test needs refactoring. It is barely readable.
@RunWith(classOf[JUnitRunner])
class TestSourceLocator extends AnyFunSuite {

  import tla._

  private val parser = DefaultType1Parser

  val types =
    Map(
        "i" -> parser("Int"),
        "b" -> parser("Bool"),
        "iiTOi" -> parser("(Int, Int) => Int"),
        "iTOi" -> parser("Int => Int"),
        "X" -> parser("Int => Int"),
        "D2" -> parser("(Int => Int, Int) => Int"),
        "TOi" -> parser("() => Int"),
        "rx" -> parser("[x: Int]"),
        "ii" -> parser("<<Int, Int>>"),
    )

  // plus(a, b) == a + b
  val decl1: TlaOperDecl =
    declOp("plus", plus(name("a") ? "i", name("b") ? "i") ? "i", OperParam("a"), OperParam("b"))
      .typedOperDecl(types, "iiTOi")

  // App(X(_), p) == X(p)
  val decl2: TlaOperDecl =
    declOp("App", appOp(name("X") ? "X", name("p") ? "i") ? "i", OperParam("X", 1), OperParam("p"))
      .typedOperDecl(types, "D2")

  val decls = List(
      decl1,
      decl2,
  )

  val nameGen = new UniqueNameGenerator
  val renaming = new IncrementalRenaming(new IdleTracker)

  // x' /\ y
  val ex1 = and(prime(name("x") ? "b") ? "b", name("y") ? "b").typed(types, "b")
  // LET A(p) == p + 1 IN
  // A(1) >= 0
  val ex2 = letIn(
      ge(appOp(name("A") ? "iTOi", int(1)) ? "i", int(0)) ? "b",
      declOp("A", plus(name("p") ? "i", int(1)) ? "i", OperParam("p"))
        .typedOperDecl(types, "iTOi"),
  ).typed(types, "b")
  // plus(x, 1)
  val ex3 = appOp(name("plus") ? "iiTOi", name("x") ? "i", int(1)).typed(types, "i")
  // LET I(p) == p IN
  // IF y THEN App(I, 0) ELSE 1
  val ex4 = letIn(
      ite(name("y") ? "b", appOp(name("App") ? "D2", name("I") ? "X", int(0)) ? "i", int(1)) ? "i",
      declOp("I", name("p") ? "i", OperParam("p")).typedOperDecl(types, "X"),
  ).typed(types, "b")
  // LET A(p, q) == IntentionallyUndefinedOper(p, q) IN
  //   LET B == b
  //       C(p) == A(p, B())
  //   IN
  //   LET D == x IN
  //   C(D())
  val ex5 =
    letIn(
        letIn(
            letIn(
                appOp(name("C") ? "iTOi", appOp(name("D") ? "TOi") ? "i") ? "i",
                declOp("D", name("x") ? "i").typedOperDecl(types, "TOi"),
            ) ? "i",
            declOp("B", name("b") ? "i").typedOperDecl(types, "TOi"),
            declOp("C", appOp(name("A") ? "iiTOi", name("p") ? "i", appOp(name("B") ? "TOi") ? "i") ? "i",
                OperParam("p"))
              .typedOperDecl(types, "iTOi"),
        ) ? "i",
        declOp("A", appOp(name("IntentionallyUndefinedOper") ? "iiTOi", name("p") ? "i", name("q") ? "i") ? "i",
            OperParam("p"), OperParam("q"))
          .typedOperDecl(types, "iiTOi"),
    ).typed(types, "i")
  // UNCHANGED x
  val ex6 = unchanged(name("x") ? "i").typed(types, "b")
  // UNCHANGED <<x, y>>
  val ex7 =
    unchanged(tuple(name("x") ? "i", name("y") ? "i") ? "ii").typed(types, "b")
  // [x |-> 1].x
  val ex9 = appFun(enumFun(str("x"), int(1)) ? "rx", str("x")).typed(types, "i")

  val exs = List(
      ex1,
      ex2,
      ex3,
      ex4,
      ex5,
      ex6,
      ex7,
      ex9,
  )

  def generateLoc(uid: UID) =
    new SourceLocation(
        "filename",
        new SourceRegion(
            new SourcePosition(uid.id.toInt),
            new SourcePosition(uid.id.toInt),
        ),
    )

  // Arbitrary assignment, all exs get a unique position equal to their UID
  val sourceMap: SourceMap =
    ((exs.map(allUidsBelow) ++ decls.map(_.body).map(allUidsBelow))
          .foldLeft(Set.empty[UID]) {
            _ ++ _
          }
          .map { x =>
            x -> generateLoc(x)
          })
      .toMap

  val exMap = new mutable.HashMap[UID, TlaEx]()

  val mapListener = new TransformationListener {
    override def onTransformation(originalEx: TlaEx, newEx: TlaEx): Unit = {
      exMap.update(originalEx.ID, originalEx)
      exMap.update(newEx.ID, newEx)
    }

    override def onDeclTransformation(originalDecl: TlaDecl, newDecl: TlaDecl): Unit = {
      // nothing added here, as onDeclTransformation is a new method
    }
  }

  val changeListener = new ChangeListener()
  val tracker = TrackerWithListeners(changeListener, mapListener)

  val locator = SourceLocator(sourceMap, changeListener)

  def testTransformation(t: TlaExTransformation): Unit = {
    val post = exs.map(t)
    val postIds = post.map(allUidsBelow).foldLeft(Set.empty[UID]) {
      _ ++ _
    }

    val failures = postIds.filterNot(i => locator.sourceOf(i).nonEmpty)
    assert(failures.isEmpty)
  }

  test("Test DeepCopy") {
    val transformation = DeepCopy(tracker).deepCopyEx[TlaEx] _

    testTransformation(transformation)
  }

  test("Test Flatten") {
    val transformation = Flatten(tracker)(Untyped)

    testTransformation(transformation)
  }

  test("Test IncrementalRenaming") {
    val transformation = new IncrementalRenaming(tracker)

    testTransformation(transformation)
  }

  test("Test Inline") {
    val transformation = new Inliner(tracker, renaming).transformEx

    testTransformation(transformation)
  }

  test("Test NoOp") {
    val transformation = tracker.trackEx {
      identity
    }

    testTransformation(transformation)
  }

  test("Test Prime") {
    val vars = Set("x", "y")
    val transformation = decorateWithPrime(vars, tracker)

    testTransformation(transformation)
  }
}
