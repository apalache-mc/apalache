package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{
  LetInEx,
  NameEx,
  OperEx,
  OperFormalParam,
  SimpleFormalParam,
  TestingPredefs,
  TlaOperDecl,
  Builder => tla
}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestParameterNormalizer
    extends FunSuite
    with BeforeAndAfterEach
    with TestingPredefs {

  val noTracker = TrackerWithListeners()
  val decisionFn: TlaOperDecl => Boolean = { _ =>
    true
  }
  var parNorm =
    new ParameterNormalizer(new UniqueNameGenerator, noTracker, decisionFn)

  override def beforeEach(): Unit = {
    parNorm =
      new ParameterNormalizer(new UniqueNameGenerator, noTracker, decisionFn)
  }

  test("Nullary: No-op") {

    // A == 1
    val decl = tla.declOp("A", 1)

    val pnf = parNorm.normalizeDeclaration(decl)

    assert(pnf == decl)

  }

  test("Simple parameter") {

    // A(p) == p
    val decl = tla.declOp("A", n_p, "p")

    val pnf = parNorm.normalizeDeclaration(decl)

    val assertCond = pnf match {
      case TlaOperDecl(name, SimpleFormalParam(p) :: Nil, body) =>
        body match {
          case LetInEx(letInBody, TlaOperDecl(newName, Nil, NameEx(`p`))) =>
            name != newName && letInBody == OperEx(
              TlaOper.apply,
              NameEx(newName)
            )
          case _ => false
        }
      case _ => false
    }

    assert(assertCond)

  }

  test("HO parameter") {

    // A(T(_)) == T(0)
    val decl = tla.declOp("A", tla.appOp(n_T, 0), ("T", 1))

    val pnf = parNorm.normalizeDeclaration(decl)

    val assertCond = pnf match {
      case TlaOperDecl(name, OperFormalParam(opName, 1) :: Nil, body) =>
        body match {
          case LetInEx(
              letInBody,
              TlaOperDecl(
                newName,
                SimpleFormalParam(fakeArg) :: Nil,
                OperEx(TlaOper.apply, NameEx(`opName`), NameEx(arg))
              )
              ) =>
            arg == fakeArg &&
              name != newName &&
              letInBody == OperEx(TlaOper.apply, NameEx(newName), 0)
          case _ => false
        }
      case _ => false
    }

    assert(assertCond)

  }

}
