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
            tla.appOp(n_A, tla.minus("p", 1)),
            tla.appOp(n_A, tla.minus("p", 1))
        ))

    decl.isRecursive = true

    val cached = cacher.cacheApplicaitons(Set(operName), Cacher.DecisionFns.recursive)(decl)
    assert(cached.isInstanceOf[TlaOperDecl])
    val asOper = cached.asInstanceOf[TlaOperDecl]
    assert(asOper.isRecursive)
    assert(asOper.body.isInstanceOf[LetInEx])
    val letInEx = asOper.body.asInstanceOf[LetInEx]

    assert(letInEx.decls.exists { decl =>
      (decl.body == tla.appOp(n_A, tla.minus("p", 1))) &&
      (letInEx.body == tla.plus(tla.appDecl(decl), tla.appDecl(decl)))
    })
  }

  test("Two expressions") {
    val operName = "A"
    val decl = TlaOperDecl(operName, List("p"),
        tla.plus(
            tla.appOp(n_A, tla.minus("p", 1)),
            tla.appOp(n_A, tla.minus("p", 2))
        ))

    decl.isRecursive = true

    val cached = cacher.cacheApplicaitons(Set(operName), Cacher.DecisionFns.recursive)(decl)
    assert(cached.isInstanceOf[TlaOperDecl])
    val asOper = cached.asInstanceOf[TlaOperDecl]
    assert(asOper.isRecursive)
    assert(asOper.body.isInstanceOf[LetInEx])
    val letInEx = asOper.body.asInstanceOf[LetInEx]

    assert(letInEx.decls.exists { decl1 =>
      (decl1.body == tla.appOp(n_A, tla.minus("p", 1))) &&
      letInEx.decls.exists { decl2 =>
        (decl2.body == tla.appOp(n_A, tla.minus("p", 2))) &&
        (letInEx.body == tla.plus(tla.appDecl(decl1), tla.appDecl(decl2)))
      }
    })
  }

  test("Nested") {
    val operName = "A"
    val decl = TlaOperDecl(operName, List("p", "q"), tla.appOp(n_A, tla.appOp(n_A, 0, "p"), "q"))

    decl.isRecursive = true

    val cached = cacher.cacheApplicaitons(Set(operName), Cacher.DecisionFns.recursive)(decl)
    assert(cached.isInstanceOf[TlaOperDecl])
    val asOper = cached.asInstanceOf[TlaOperDecl]
    assert(asOper.isRecursive)
    assert(asOper.body.isInstanceOf[LetInEx])
    val letInEx = asOper.body.asInstanceOf[LetInEx]

    assert(letInEx.decls.exists { decl1 =>
      (decl1.body == tla.appOp(n_A, 0, "p")) &&
      letInEx.decls.exists { decl2 =>
        (decl2.body == tla.appOp(n_A, tla.appDecl(decl1), "q")) &&
        (letInEx.body == tla.appDecl(decl2))
      }
    })
  }

  test("Inner recursive LET-IN") {
    val operName = "A"

    val operNames = Set("B") // does not contain A

    val declT = tla.declOp("T", tla.appOp(n_T, n_x), "x")
    declT.isRecursive = true

    val decl = TlaOperDecl(operName, List.empty,
        tla.plus(1,
            tla.letIn(
                tla.plus(
                    tla.appOp(n_T, 0),
                    tla.appOp(n_B, 1)
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
            declB1.body == tla.appOp(n_B, 1) && (
                body match {
                  case OperEx(TlaArithOper.plus, `one`, LetInEx(letInBody, defs @ _*)) =>
                    (defs exists { declT0 =>
                      (declT0.body == tla.appOp(n_T, 0)) &&
                      letInBody == tla.plus(tla.appDecl(declT0), tla.appDecl(declB1))
                    }) &&
                      (
                          defs exists { declT =>
                            declT.body match {
                              case LetInEx(tbody, declTx) =>
                                declTx.body == tla.appOp(n_T, n_x) &&
                                  tbody == tla.appDecl(declTx)
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
