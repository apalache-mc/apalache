package at.forsyte.apalache.io.json

import at.forsyte.apalache.io.json.impl.{TlaToUJson, UJsonToTla}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.io.{TypeTagPrinter, UntypedReader}

@RunWith(classOf[JUnitRunner])
class TestUJsonToTla extends FunSuite with BeforeAndAfterEach with TestingPredefs {
  implicit val reader = UntypedReader
  implicit val printer = new TypeTagPrinter {
    override def apply(tag: TypeTag): String = ""
  }

  val dec = new UJsonToTla(sourceStoreOpt = None)
  val enc = new TlaToUJson(locatorOpt = None)

  test("dec(enc(x)) =?= x") {
    val exs: Seq[TlaEx] = Seq(
        tla.and(tla.name("x"), tla.bool(true)),
        tla.ite(tla.name("p"), tla.name("A"), tla.name("B")),
        tla.letIn(
            tla.appOp(tla.name("A"), tla.int(1)),
            tla
              .declOp(
                  "A",
                  tla.plus(tla.name("p"), tla.int(1)),
                  OperParam("p")
              )
              .withTag(Untyped())
              .asInstanceOf[TlaOperDecl]
        )
    )

    exs foreach { ex =>
      assert(dec.asTlaEx(enc(ex)) == ex)
    }

    val decls: Seq[TlaDecl] = Seq(
        tla.declOp("X", tla.eql(tla.name("a"), tla.int(1)), OperParam("a")),
        TlaAssumeDecl(tla.eql(tla.int(1), tla.int(0))),
        TlaConstDecl("c"),
        TlaVarDecl("v")
    )

    decls foreach { decl =>
      assert(dec.asTlaDecl(enc(decl)) == decl)
    }

    val modules: Seq[TlaModule] = Seq(
        new TlaModule("Empty", Seq.empty),
        new TlaModule("Module", decls)
    )

    modules foreach { m =>
      assert(dec.asTlaModule(enc(m)) == m)
    }

    assert(dec.fromRoot(enc.makeRoot(modules)) == modules)
  }

}
