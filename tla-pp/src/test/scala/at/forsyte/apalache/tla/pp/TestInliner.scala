package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.pp.Inliner.emptyScope
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestInliner extends AnyFunSuite with BeforeAndAfterEach {

  import Inliner.Scope

  def mkModule(decls: TlaDecl*): TlaModule = TlaModule("M", decls)

  var inliner = new Inliner(new IdleTracker, new UniqueNameGenerator)

  def runFresh[T](scopeFn: Scope => T): T = scopeFn(Inliner.emptyScope)

  override def beforeEach(): Unit = {
    inliner = new Inliner(new IdleTracker, new UniqueNameGenerator)
  }

  test("Test LET inline: LET A(p) == e IN A(x) ~~> e[x/p]") {

    val ABody = tla.plus(tla.name("p").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())
    val AType = OperT1(Seq(IntT1()), IntT1())
    val ADecl = TlaOperDecl("A", List(OperParam("p")), ABody)(Typed(AType))
    val AApp = tla.appOp(tla.name(ADecl.name).as(AType), tla.name("x").as(IntT1())).as(IntT1())

    val letInEx = tla.letIn(AApp, ADecl).as(IntT1())

    val expectedBody = tla.plus(tla.name("x").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())

    val actualBody = runFresh(inliner.transform(_)(letInEx))

    assert(actualBody == expectedBody)
  }

  test("Test global inline: A(p) == e, A(x) ~~> e[x/p]") {
    val ABody = tla.plus(tla.name("p").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())
    val AType = OperT1(Seq(IntT1()), IntT1())
    val ADecl = TlaOperDecl("A", List(OperParam("p")), ABody)(Typed(AType))
    val AApp = tla.appOp(tla.name(ADecl.name).as(AType), tla.name("x").as(IntT1())).as(IntT1())

    val expectedBody = tla.plus(tla.name("x").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())

    val scope = Map(ADecl.name -> ADecl)

    val actualBody = inliner.transform(scope)(AApp)

    assert(actualBody == expectedBody)
  }

  test("Test nested LET-IN: LET P(x,y) == LET Q(z) == z + y IN Q(x) IN P(1,2) ~~> 1 + 2 ") {
    val QBody = tla.plus(tla.name("z").as(IntT1()), tla.name("y").as(IntT1())).as(IntT1())
    val QType = OperT1(Seq(IntT1()), IntT1())
    val QDecl = TlaOperDecl("Q", List(OperParam("z")), QBody)(Typed(QType))
    val PBody = tla
      .letIn(
          tla
            .appOp(
                tla.name("Q").as(QType),
                tla.name("x").as(IntT1()),
            )
            .as(IntT1()),
          QDecl,
      )
      .as(IntT1())
    val PType = OperT1(Seq(IntT1(), IntT1()), IntT1())
    val PDecl = TlaOperDecl("P", List(OperParam("x"), OperParam("y")), PBody)(Typed(PType))

    val toplevel = tla
      .letIn(
          tla
            .appOp(
                tla.name("P").as(PType),
                tla.int(1).as(IntT1()),
                tla.int(2).as(IntT1()),
            )
            .as(IntT1()),
          PDecl,
      )
      .as(IntT1())

    val expectedBody = tla.plus(tla.int(1).as(IntT1()), tla.int(2).as(IntT1())).as(IntT1())

    val scope = emptyScope

    val actualBody = inliner.transform(scope)(toplevel)

    assert(actualBody == expectedBody)
  }

}
