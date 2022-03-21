package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir
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

  var inlinerKeepNullary = new Inliner(new IdleTracker, new UniqueNameGenerator)
  var inlinerInlineNullary = new Inliner(new IdleTracker, new UniqueNameGenerator, keepNullary = false)

  def runFresh[T](scopeFn: Scope => T): T = scopeFn(Inliner.emptyScope)

  override def beforeEach(): Unit = {
    inlinerKeepNullary = new Inliner(new IdleTracker, new UniqueNameGenerator)
    inlinerInlineNullary = new Inliner(new IdleTracker, new UniqueNameGenerator, keepNullary = false)
  }

  test("LET inline: LET A(p) == e IN A(x) ~~> e[x/p]") {

    val ABody = tla.plus(tla.name("p").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())
    val AType = OperT1(Seq(IntT1()), IntT1())
    val ADecl = TlaOperDecl("A", List(OperParam("p")), ABody)(Typed(AType))
    val AApp = tla.appOp(tla.name(ADecl.name).as(AType), tla.name("x").as(IntT1())).as(IntT1())

    val letInEx = tla.letIn(AApp, ADecl).as(IntT1())

    val expectedBody = tla.plus(tla.name("x").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())

    val actualBody = runFresh(inlinerKeepNullary.transform(_)(letInEx))

    assert(actualBody == expectedBody)
  }

  test("Global inline: A(p) == e, A(x) ~~> e[x/p]") {
    val ABody = tla.plus(tla.name("p").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())
    val AType = OperT1(Seq(IntT1()), IntT1())
    val ADecl = TlaOperDecl("A", List(OperParam("p")), ABody)(Typed(AType))
    val AApp = tla.appOp(tla.name(ADecl.name).as(AType), tla.name("x").as(IntT1())).as(IntT1())

    val expectedBody = tla.plus(tla.name("x").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())

    val scope = Map(ADecl.name -> ADecl)

    val actualBody = inlinerKeepNullary.transform(scope)(AApp)

    assert(actualBody == expectedBody)
  }

  test("Nested LET-IN: LET P(x,y) == LET Q(z) == z + y IN Q(x) IN P(1,2) ~~> 1 + 2 ") {
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

    val actualBody = inlinerKeepNullary.transform(emptyScope)(toplevel)

    assert(actualBody == expectedBody)
  }

  test("Linear dependencies: P(x) == Q(x) + 1; Q(z) == z + 1; P(1) ~~> 1 + 1 + 1 ") {
    val QBody = tla.plus(tla.name("z").as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())
    val QType = OperT1(Seq(IntT1()), IntT1())
    val QDecl = TlaOperDecl("Q", List(OperParam("z")), QBody)(Typed(QType))
    val PBody =
      tla
        .plus(tla
              .appOp(
                  tla.name("Q").as(QType),
                  tla.name("x").as(IntT1()),
              )
              .as(IntT1()), tla.int(1).as(IntT1()))
        .as(IntT1())

    val PType = OperT1(Seq(IntT1()), IntT1())
    val PDecl = TlaOperDecl("P", List(OperParam("x")), PBody)(Typed(PType))

    val XDecl = TlaOperDecl("X", List.empty,
        tla
          .appOp(
              tla.name("P").as(PType),
              tla.int(1).as(IntT1()),
          )
          .as(IntT1()))(Typed(OperT1(Seq.empty, IntT1())))

    val expectedBody =
      tla.plus(tla.plus(tla.int(1).as(IntT1()), tla.int(1).as(IntT1())).as(IntT1()), tla.int(1).as(IntT1())).as(IntT1())

    val decls = List(QDecl, PDecl, XDecl)
    val module = mkModule(decls: _*)

    val txModule = inlinerKeepNullary.apply(module)

    val actualBody = txModule.declarations(2).asInstanceOf[TlaOperDecl].body

    assert(actualBody == expectedBody)
  }

  test("KeepNullary: LET A == 1 B(x) == 2 IN A + B(0) ~~> LET A == 1 IN A + 2 or 1 + 2") {
    val ABody = tla.int(1).as(IntT1())
    val AType = OperT1(Seq.empty, IntT1())
    val ADecl = TlaOperDecl("A", List.empty, ABody)(Typed(AType))

    val BBody = tla.int(2).as(IntT1())
    val BType = OperT1(Seq(IntT1()), IntT1())
    val BDecl = TlaOperDecl("B", List(OperParam("x")), BBody)(Typed(BType))

    val AApp = tla.appOp(tla.name("A").as(AType)).as(IntT1())
    val BApp = tla.appOp(tla.name("B").as(BType), tla.int(0).as(IntT1())).as(IntT1())

    val ex = LetInEx(tla.plus(AApp, BApp).as(IntT1()), ADecl, BDecl)(Typed(IntT1()))
    val expectedIfKeep = LetInEx(tla.plus(AApp, tla.int(2).as(IntT1())).as(IntT1()), ADecl)(Typed(IntT1()))
    val expectedIfInline = tla.plus(tla.int(1).as(IntT1()), tla.int(2).as(IntT1())).as(IntT1())
    val actualKeep = inlinerKeepNullary.transform(emptyScope)(ex)

    assert(actualKeep == expectedIfKeep)

    val actualInline = inlinerInlineNullary.transform(emptyScope)(ex)

    assert(actualInline == expectedIfInline)

  }

}
