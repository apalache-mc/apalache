package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

import scala.math.BigInt

@RunWith(classOf[JUnitRunner])
class TestUnroller extends FunSuite with BeforeAndAfterEach with TestingPredefs {

  val noTracker = TrackerWithListeners()
  private var unroller = new Unroller(new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker))

  override def beforeEach(): Unit = {
    unroller = new Unroller(new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker))
  }

  def exAsDecl(pa: (String, TlaEx)): TlaOperDecl = TlaOperDecl(pa._1, List.empty, pa._2)

  test("No-op") {
    val decls = Seq[(String, TlaEx)](
        ("A", "1"),
        ("B", 0),
        ("C", tla.and(n_x, n_P)),
        ("D", tla.letIn(n_T, tla.declOp("T", tla.name("p"), "p").untypedOperDecl()))
    ) map exAsDecl

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    assert(module.declarations == unrolled.declarations)
  }

  test("0 step: ParamNormalForm") {
    val name = "A"

    // A(p) == A(p)
    val recDecl = tla.declOp(name, tla.appOp(n_A, n_p), "p").untypedOperDecl()
    recDecl.isRecursive = true

    val defaultVal: BigInt = 42

    val decls = recDecl +: (Seq[(String, TlaEx)](
        (Unroller.UNROLL_TIMES_PREFIX + name, 0),
        (Unroller.UNROLL_DEFAULT_PREFIX + name, defaultVal.intValue)
    ) map exAsDecl)

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    val newAOpt = unrolled.operDeclarations.find(_.name == name)

    val assertCond = newAOpt.exists { case d @ TlaOperDecl(_, _, body) =>
      !d.isRecursive &&
        (body match {
          case LetInEx(ValEx(TlaInt(`defaultVal`)), TlaOperDecl(_, Nil, NameEx("p"))) =>
            true
          case _ => false
        })
    }

    assert(assertCond)
  }

  test("1 step: Nontrivial inlining") {
    val name = "A"

    // A(p) == A(p)
    val recDecl = tla.declOp(name, tla.appOp(n_A, n_p), "p").untypedOperDecl()
    recDecl.isRecursive = true

    val defaultVal: BigInt = 42

    val decls = recDecl +: (Seq[(String, TlaEx)](
        (Unroller.UNROLL_TIMES_PREFIX + name, 1),
        (Unroller.UNROLL_DEFAULT_PREFIX + name, defaultVal.intValue)
    ) map exAsDecl)

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    val newAOpt = unrolled.operDeclarations.find(_.name == name)

    newAOpt match {
      case Some(d @ TlaOperDecl(_, _, body)) =>
        assert(!d.isRecursive)

        body match {
          case LetInEx(paramNormalBody, TlaOperDecl(uniqueName, Nil, NameEx("p"))) =>
            paramNormalBody match {
              case LetInEx(defaultBody, TlaOperDecl(_, Nil, OperEx(TlaOper.apply, NameEx(defaultName)))) =>
                assert(ValEx(TlaInt(defaultVal)) == defaultBody)
                assert(uniqueName == defaultName)

              case _ =>
                fail("Expected second LetInEx")
            }

          case _ =>
            fail("Expected first LetInEx")
        }

      case None =>
        fail("Expected Some(TlaOperDecl(...))")
    }

  }

  test("Recursive LET-IN inside non-recursive operator") {
    val letInOpName = "A"

    // A(p) == A(p)
    val recDecl = tla.declOp(letInOpName, tla.appOp(n_A, n_p), "p").untypedOperDecl()
    recDecl.isRecursive = true

    val appEx = tla.appDecl(recDecl, tla.int(99)).untyped()
    // X == LET A(p) == A(p) IN A(99)
    val nonRecDecl = tla.declOp("X", tla.letIn(appEx, recDecl)).untypedOperDecl()

    val defaultVal: BigInt = 42

    val decls = nonRecDecl +: (Seq[(String, TlaEx)](
        (Unroller.UNROLL_TIMES_PREFIX + letInOpName, 1),
        (Unroller.UNROLL_DEFAULT_PREFIX + letInOpName, defaultVal.intValue)
    ) map exAsDecl)

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    val newXOpt = unrolled.operDeclarations.find(_.name == "X")

    // The test is: Does an embedded LET-IN get unrolled in the same way as a top-level declaration

    // reset Renaming
    unroller = new Unroller(new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker))

    val altDecls = recDecl +: (Seq[(String, TlaEx)](
        (Unroller.UNROLL_TIMES_PREFIX + letInOpName, 1),
        (Unroller.UNROLL_DEFAULT_PREFIX + letInOpName, defaultVal.intValue)
    ) map exAsDecl)

    val altModule = new TlaModule("N", altDecls)
    val altUnrolled = unroller(altModule)

    val aUnrolledOpt = altUnrolled.operDeclarations.find(_.name == letInOpName)

    assert(aUnrolledOpt.nonEmpty)

    val aUnrolledBody = aUnrolledOpt.get.body

    // explicit matching and assertions instead of smart and error-prone computations
    newXOpt match {
      case Some(TlaOperDecl(_, _, body)) =>
        body match {
          case LetInEx(letBody, TlaOperDecl(declName, params, unrolled)) =>
            assert(appEx == letBody)
            assert(letInOpName == declName)
            assert(List(SimpleFormalParam("p")) == params)
            assert(aUnrolledBody == unrolled)

          case _ =>
            fail("The unrolled body does not match the pattern")
        }

      case None =>
        fail("Expected TlaOperDecl")
    }
  }

}
