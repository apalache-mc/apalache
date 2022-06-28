package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.Inliner.emptyScope
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestInliner extends AnyFunSuite with BeforeAndAfterEach {

  import Inliner.Scope

  def mkModule(decls: TlaDecl*): TlaModule = TlaModule("M", decls)

  var renaming = new IncrementalRenaming(new IdleTracker)
  var inlinerKeepNullary = new Inliner(new IdleTracker, renaming)
  var inlinerInlineNullary = new Inliner(new IdleTracker, renaming, keepNullaryMono = false)

  def runFresh[T](scopeFn: Scope => T): T = scopeFn(Inliner.emptyScope)

  override def beforeEach(): Unit = {
    renaming = new IncrementalRenaming(new IdleTracker)
    inlinerKeepNullary = new Inliner(new IdleTracker, renaming)
    inlinerInlineNullary = new Inliner(new IdleTracker, renaming, keepNullaryMono = false)
  }

  test("LET inline: LET A(p) == e IN A(x) ~~> e[x/p]") {

    val ABody = tla.plus(tla.name("p").as(IntT1), tla.int(1).as(IntT1)).as(IntT1)
    val AType = OperT1(Seq(IntT1), IntT1)
    val ADecl = TlaOperDecl("A", List(OperParam("p")), ABody)(Typed(AType))
    val AApp = tla.appOp(tla.name(ADecl.name).as(AType), tla.name("x").as(IntT1)).as(IntT1)

    val letInEx = tla.letIn(AApp, ADecl).as(IntT1)

    val expectedBody = tla.plus(tla.name("x").as(IntT1), tla.int(1).as(IntT1)).as(IntT1)

    val actualBody = runFresh(inlinerKeepNullary.transform(_)(letInEx))

    assert(actualBody == expectedBody)
  }

  test("Global inline: A(p) == e, A(x) ~~> e[x/p]") {
    val ABody = tla.plus(tla.name("p").as(IntT1), tla.int(1).as(IntT1)).as(IntT1)
    val AType = OperT1(Seq(IntT1), IntT1)
    val ADecl = TlaOperDecl("A", List(OperParam("p")), ABody)(Typed(AType))
    val AApp = tla.appOp(tla.name(ADecl.name).as(AType), tla.name("x").as(IntT1)).as(IntT1)

    val expectedBody = tla.plus(tla.name("x").as(IntT1), tla.int(1).as(IntT1)).as(IntT1)

    val scope = Map(ADecl.name -> ADecl)

    val actualBody = inlinerKeepNullary.transform(scope)(AApp)

    assert(actualBody == expectedBody)
  }

  test("Nested LET-IN: LET P(x,y) == LET Q(z) == z + y IN Q(x) IN P(1,2) ~~> 1 + 2 ") {
    val QBody = tla.plus(tla.name("z").as(IntT1), tla.name("y").as(IntT1)).as(IntT1)
    val QType = OperT1(Seq(IntT1), IntT1)
    val QDecl = TlaOperDecl("Q", List(OperParam("z")), QBody)(Typed(QType))
    val PBody = tla
      .letIn(
          tla
            .appOp(
                tla.name("Q").as(QType),
                tla.name("x").as(IntT1),
            )
            .as(IntT1),
          QDecl,
      )
      .as(IntT1)
    val PType = OperT1(Seq(IntT1, IntT1), IntT1)
    val PDecl = TlaOperDecl("P", List(OperParam("x"), OperParam("y")), PBody)(Typed(PType))

    val toplevel = tla
      .letIn(
          tla
            .appOp(
                tla.name("P").as(PType),
                tla.int(1).as(IntT1),
                tla.int(2).as(IntT1),
            )
            .as(IntT1),
          PDecl,
      )
      .as(IntT1)

    val expectedBody = tla.plus(tla.int(1).as(IntT1), tla.int(2).as(IntT1)).as(IntT1)

    val actualBody = inlinerKeepNullary.transform(emptyScope)(toplevel)

    assert(actualBody == expectedBody)
  }

  test("Linear dependencies: P(x) == Q(x) + 1; Q(z) == z + 1; P(1) ~~> 1 + 1 + 1 ") {
    val QBody = tla.plus(tla.name("z").as(IntT1), tla.int(1).as(IntT1)).as(IntT1)
    val QType = OperT1(Seq(IntT1), IntT1)
    val QDecl = TlaOperDecl("Q", List(OperParam("z")), QBody)(Typed(QType))
    val PBody =
      tla
        .plus(tla
              .appOp(
                  tla.name("Q").as(QType),
                  tla.name("x").as(IntT1),
              )
              .as(IntT1), tla.int(1).as(IntT1))
        .as(IntT1)

    val PType = OperT1(Seq(IntT1), IntT1)
    val PDecl = TlaOperDecl("P", List(OperParam("x")), PBody)(Typed(PType))

    val XDecl = TlaOperDecl("X", List.empty,
        tla
          .appOp(
              tla.name("P").as(PType),
              tla.int(1).as(IntT1),
          )
          .as(IntT1))(Typed(OperT1(Seq.empty, IntT1)))

    val expectedBody =
      tla.plus(tla.plus(tla.int(1).as(IntT1), tla.int(1).as(IntT1)).as(IntT1), tla.int(1).as(IntT1)).as(IntT1)

    val decls = List(QDecl, PDecl, XDecl)
    val module = mkModule(decls: _*)

    val txModule = inlinerKeepNullary.transformModule(module)

    val actualBody = txModule.declarations(2).asInstanceOf[TlaOperDecl].body

    assert(actualBody == expectedBody)
  }

  test("KeepNullary: LET A == 1 B(x) == 2 IN A + B(0) ~~> LET A == 1 IN A + 2 or 1 + 2") {
    val ABody = tla.int(1).as(IntT1)
    val AType = OperT1(Seq.empty, IntT1)
    val ADecl = TlaOperDecl("A", List.empty, ABody)(Typed(AType))

    val BBody = tla.int(2).as(IntT1)
    val BType = OperT1(Seq(IntT1), IntT1)
    val BDecl = TlaOperDecl("B", List(OperParam("x")), BBody)(Typed(BType))

    val AApp = tla.appOp(tla.name("A").as(AType)).as(IntT1)
    val BApp = tla.appOp(tla.name("B").as(BType), tla.int(0).as(IntT1)).as(IntT1)

    val ex = LetInEx(tla.plus(AApp, BApp).as(IntT1), ADecl, BDecl)(Typed(IntT1))
    val expectedIfKeep = LetInEx(tla.plus(AApp, tla.int(2).as(IntT1)).as(IntT1), ADecl)(Typed(IntT1))
    val expectedIfInline = tla.plus(tla.int(1).as(IntT1), tla.int(2).as(IntT1)).as(IntT1)
    val actualKeep = inlinerKeepNullary.transform(emptyScope)(ex)

    assert(actualKeep == expectedIfKeep)

    val actualInline = inlinerInlineNullary.transform(emptyScope)(ex)

    assert(actualInline == expectedIfInline)

  }

  test("call-by-name inline: LET A(x, y) == 1 IN FoldSet(A, v, S) ~~> FoldSet( LET AA(x,y) == 1 IN AA, v, S)") {
    val ABody = tla.int(1).as(IntT1)
    val AType = OperT1(Seq(IntT1, IntT1), IntT1)
    val AParams = List(OperParam("x"), OperParam("y"))
    val ADecl = TlaOperDecl("A", AParams, ABody)(Typed(AType))

    val n_v = tla.name("v").as(IntT1)
    val n_S = tla.name("S").as(SetT1(IntT1))

    val ex = tla
      .letIn(
          OperEx(ApalacheOper.foldSet, tla.name("A").as(AType), n_v, n_S)(Typed(IntT1)),
          ADecl,
      )
      .as(IntT1)
    val actual = inlinerKeepNullary.transform(emptyScope)(ex)

    // The localized name is an implementation detail
    val cond = actual match {
      case OperEx(ApalacheOper.foldSet, LetInEx(NameEx(genName), TlaOperDecl(opName, AParams, ABody)), _, _) =>
        opName == genName
      case _ => false
    }

    assert(cond)

  }

  test("call-by-name in nested scope: NestedCallByName.tla ") {
    val FBody = tla.name("new").as(IntT1)
    val FType = OperT1(Seq(IntT1, IntT1), IntT1)
    val FDecl = TlaOperDecl("F", List(OperParam("old"), OperParam("new")), FBody)(Typed(FType))
    val innerFold =
      OperEx(
          ApalacheOper.foldSeq,
          tla.name("F").as(FType),
          tla.name("x").as(IntT1),
          tla.tuple(tla.name("y").as(IntT1)).as(SeqT1(IntT1)),
      )(Typed(IntT1))

    val ABody = tla.letIn(innerFold, FDecl).as(IntT1)
    val ATtype = FType
    val ADecl = TlaOperDecl("A", List(OperParam("x"), OperParam("y")), ABody)(Typed(ATtype))

    val invBody =
      OperEx(
          ApalacheOper.foldSeq,
          tla.name("A").as(ATtype),
          tla.int(0).as(IntT1),
          tla.tuple(tla.int(1).as(IntT1)).as(SeqT1(IntT1)),
      )(Typed(IntT1))

    val InvDecl = TlaOperDecl("Inv", List.empty, invBody)(Typed(IntT1))

    val decls = List(ADecl, InvDecl)
    val module = mkModule(decls: _*)

    val txModule = inlinerKeepNullary.transformModule(module)

    val actualBody = txModule.declarations(1).asInstanceOf[TlaOperDecl].body

    val cond = actualBody match {
      case OperEx(ApalacheOper.foldSeq, LetInEx(NameEx(outerNameInBody), decl), _, _) =>
        decl match {
          case TlaOperDecl(outerOpName, _,
                  OperEx(ApalacheOper.foldSeq, LetInEx(NameEx(innerNameInBody), innerDecl), _, _))
              if outerNameInBody == outerOpName =>
            innerDecl match {
              case TlaOperDecl(innerOpName, _, _) => innerNameInBody == innerOpName
              case _                              => false
            }
          case _ => false
        }
      case _ => false
    }

    assert(cond)

  }

  test("Nullary global operators get inlined") {
    val ABody = tla.int(0).as(IntT1)
    val AType = OperT1(Seq.empty, IntT1)
    val ADecl = TlaOperDecl("A", List.empty, ABody)(Typed(AType))

    val BBody = tla.appOp(tla.name("A").as(AType)).as(IntT1)
    val BDecl = TlaOperDecl("B", List.empty, BBody)(Typed(AType))

    val decls = List(ADecl, BDecl)
    val module = mkModule(decls: _*)

    val txModule = inlinerKeepNullary.transformModule(module)

    val actualBody = txModule.declarations(1).asInstanceOf[TlaOperDecl].body

    assert(actualBody == ABody)
  }

  test("Inlining works correctly on nonbasic arguments:  B == e, A(x) == x, A(B()) ~~> e") {
    val BBody = tla.int(0).as(IntT1)
    val BType = OperT1(Seq.empty, IntT1)
    val BDecl = TlaOperDecl("B", List.empty, BBody)(Typed(BType))

    val ABody = tla.name("x").as(IntT1)
    val AType = OperT1(Seq(IntT1), IntT1)
    val ADecl = TlaOperDecl("A", List(OperParam("x")), ABody)(Typed(AType))

    val ex = tla.appOp(tla.name("A").as(AType), tla.appOp(tla.name("B").as(BType)).as(IntT1)).as(IntT1)

    val scope = Map(ADecl.name -> ADecl, BDecl.name -> BDecl)

    val actual = inlinerKeepNullary.transform(scope)(ex)

    assert(actual == BBody)
  }

  test("Call-by-name not deleted") {
    // A(x) ==
    //   LET F(p,q) == x IN
    //   FoldSet(F, v, S)

    val FBody = tla.name("x").as(IntT1)
    val FType = OperT1(Seq(IntT1, IntT1), IntT1)
    val FDecl = TlaOperDecl("F", List(OperParam("p"), OperParam("q")), FBody)(Typed(FType))

    val n_v = tla.name("v").as(IntT1)
    val n_S = tla.name("S").as(SetT1(IntT1))

    val ABody = tla
      .letIn(
          OperEx(ApalacheOper.foldSet, tla.name("F").as(FType), n_v, n_S)(Typed(IntT1)),
          FDecl,
      )
      .as(IntT1)

    val AType = OperT1(Seq(IntT1), IntT1)
    val ADecl = TlaOperDecl("A", List(OperParam("x")), ABody)(Typed(AType))

    val arg = tla.int(0).as(IntT1)
    val ex = tla.appOp(tla.name("A").as(AType), arg).as(IntT1)

    val tmpDecl = TlaOperDecl("X", List.empty, ex)(Typed(OperT1(Seq.empty, IntT1)))

    val decls = List(ADecl, tmpDecl)

    val module = mkModule(decls: _*)

    val txModule = inlinerKeepNullary.transformModule(module)

    val actualBody = txModule.declarations(1).asInstanceOf[TlaOperDecl].body

    val cond = actualBody match {
      case OperEx(ApalacheOper.foldSet, letInEx: LetInEx, _, _) =>
        Inliner.isPassByName(letInEx) && letInEx.decls.head.body == arg
      case _ => false
    }

    assert(cond)
  }

  test("Lambda passed to HO oper: A(F(_)) = F(x); A(LAMBDA p: p + 1) ~~> x + 1") {
    val FType = OperT1(Seq(IntT1), IntT1)
    val ABody = tla.appOp(tla.name("F").as(FType), tla.name("x").as(IntT1)).as(IntT1)
    val AType = OperT1(Seq(FType), IntT1)
    val ADecl = TlaOperDecl("A", List(OperParam("F", 1)), ABody)(Typed(AType))
    val lambda = tla
      .letIn(
          tla.name("LAMBDA").as(FType),
          TlaOperDecl(
              "LAMBDA",
              List(OperParam("p")),
              tla.plus(tla.name("p").as(IntT1), tla.int(1).as(IntT1)).as(IntT1),
          )(Typed(FType)),
      )
      .as(FType)
    val ex = tla.appOp(tla.name("A").as(AType), lambda).as(IntT1)

    val expected = tla.plus(tla.name("x").as(IntT1), tla.int(1).as(IntT1)).as(IntT1)

    val scope = Map("A" -> ADecl) // we know no inlining is needed in ADecl, so we can manually build scope

    val actual = inlinerKeepNullary.transform(scope)(ex)

    assert(expected == actual)
  }

}
