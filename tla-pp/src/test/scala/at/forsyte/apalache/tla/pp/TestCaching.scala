package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import UntypedPredefs._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestCaching extends FunSuite with BeforeAndAfterEach with TestingPredefs {
  private var cacher = new Cacher(new UniqueNameGenerator, TrackerWithListeners())

  override def beforeEach(): Unit = {
    cacher = new Cacher(new UniqueNameGenerator, TrackerWithListeners())
  }

  test("Single expression") {
    val operName = "A"
    val decl = TlaOperDecl(operName, List("p"),
        tla.plus(
            tla.appOp(n_A, tla.minus(name("p"), tla.int(1))),
            tla.appOp(n_A, tla.minus(name("p"), tla.int(1)))
        ))(Untyped())

    decl.isRecursive = true

    val cached = cacher.cacheApplicaitons(Set(operName), Cacher.DecisionFns.recursive)(decl)
    assert(cached.isInstanceOf[TlaOperDecl])
    val asOper = cached.asInstanceOf[TlaOperDecl]
    assert(asOper.isRecursive)
    assert(asOper.body.isInstanceOf[LetInEx])
    val letInEx = asOper.body.asInstanceOf[LetInEx]

    assert(letInEx.decls.exists { decl =>
      (decl.body == tla.appOp(n_A, tla.minus(tla.name("p"), tla.int(1))).untyped()) &&
      (letInEx.body == tla.plus(tla.appDecl(decl), tla.appDecl(decl)).untyped())
    })
  }

  test("Two expressions") {
    val operName = "A"
    val decl = TlaOperDecl(operName, List("p"),
        tla.plus(
            tla.appOp(n_A, tla.minus(tla.name("p"), tla.int(1))),
            tla.appOp(n_A, tla.minus(tla.name("p"), tla.int(2)))
        ))(Untyped())

    decl.isRecursive = true

    val cached = cacher.cacheApplicaitons(Set(operName), Cacher.DecisionFns.recursive)(decl)
    assert(cached.isInstanceOf[TlaOperDecl])
    val asOper = cached.asInstanceOf[TlaOperDecl]
    assert(asOper.isRecursive)
    assert(asOper.body.isInstanceOf[LetInEx])
    val letInEx = asOper.body.asInstanceOf[LetInEx]

    assert(letInEx.decls.exists { decl1 =>
      (decl1.body == tla.appOp(n_A, tla.minus(tla.name("p"), tla.int(1))).untyped()) &&
      letInEx.decls.exists { decl2 =>
        (decl2.body == tla.appOp(n_A, tla.minus(tla.name("p"), tla.int(2))).untyped()) &&
        (letInEx.body == tla.plus(tla.appDecl(decl1), tla.appDecl(decl2)).untyped())
      }
    })
  }

  test("Nested") {
    val operName = "A"
    val decl =
      TlaOperDecl(operName, List("p", "q"), tla.appOp(n_A, tla.appOp(n_A, tla.int(0), tla.name("p")), tla.name("q")))(
          Untyped())

    decl.isRecursive = true

    val cached = cacher.cacheApplicaitons(Set(operName), Cacher.DecisionFns.recursive)(decl)
    assert(cached.isInstanceOf[TlaOperDecl])
    val asOper = cached.asInstanceOf[TlaOperDecl]
    assert(asOper.isRecursive)
    assert(asOper.body.isInstanceOf[LetInEx])
    val letInEx = asOper.body.asInstanceOf[LetInEx]

    assert(letInEx.decls.exists { decl1 =>
      (decl1.body == tla.appOp(n_A, tla.int(0), tla.name("p")).untyped()) &&
      letInEx.decls.exists { decl2 =>
        (decl2.body == tla.appOp(n_A, tla.appDecl(decl1), tla.name("q")).untyped()) &&
        (letInEx.body == tla.appDecl(decl2).untyped())
      }
    })
  }

  test("Inner recursive LET-IN") {
    val operName = "A"

    val operNames = Set("B") // does not contain A

    val declT = tla.declOp("T", tla.appOp(n_T, n_x), "x").untypedOperDecl()
    declT.isRecursive = true

    val decl = TlaOperDecl(operName, List.empty,
        tla.plus(tla.int(1),
            tla.letIn(
                tla.plus(
                    tla.appOp(n_T, tla.int(0)),
                    tla.appOp(n_B, tla.int(1))
                ),
                declT
            )))

    decl.isRecursive = false

    val cached = cacher.cacheApplicaitons(operNames, Cacher.DecisionFns.recursive)(decl)
    assert(cached.isInstanceOf[TlaOperDecl])
    val asOper = cached.asInstanceOf[TlaOperDecl]
    assert(!asOper.isRecursive)

    val one: TlaEx = tla.int(1)

    assert(
        asOper.body match {
          case LetInEx(body, declB1) =>
            declB1.body == tla.appOp(n_B, tla.int(1)).untyped() && (
                body match {
                  case OperEx(TlaArithOper.plus, `one`, LetInEx(letInBody, defs @ _*)) =>
                    (defs exists { declT0 =>
                      (declT0.body == tla.appOp(n_T, tla.int(0)).untyped()) &&
                      letInBody == tla.plus(tla.appDecl(declT0), tla.appDecl(declB1)).untyped()
                    }) &&
                      (
                          defs exists { declT =>
                            declT.body match {
                              case LetInEx(tbody, declTx) =>
                                declTx.body == tla.appOp(n_T, n_x).untyped() &&
                                  tbody == tla.appDecl(declTx).untyped()
                              case _ => false
                            }
                          }
                      )
                  case _ => false
                }
            )
          case _ => false
        }
    )
  }
}
