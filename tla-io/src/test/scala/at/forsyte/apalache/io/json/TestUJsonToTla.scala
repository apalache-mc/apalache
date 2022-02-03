package at.forsyte.apalache.io.json

import at.forsyte.apalache.io.json.impl.{DefaultTagReader, TlaToUJson, UJsonToTla}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs
import org.scalacheck.Prop
import org.scalacheck.Prop.{AnyOperators, all, forAll, passed}
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers
import org.scalatest.{AppendedClues, Matchers}

@RunWith(classOf[JUnitRunner])
class TestUJsonToTla extends FunSuite with Checkers {
  implicit val reader = DefaultTagReader
  implicit val printer = TlaType1PrinterPredefs.printer

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
                  OperParam("p"),
              )
              .withTag(Untyped())
              .asInstanceOf[TlaOperDecl],
        ),
    )

    exs foreach { ex =>
      val encEx = enc(ex)
      val decEx = dec.asTlaEx(encEx)
      assert(decEx == ex)
    }

    val decls: Seq[TlaDecl] = Seq(
        tla.declOp("X", tla.eql(tla.name("a"), tla.int(1)), OperParam("a")),
        TlaAssumeDecl(tla.eql(tla.int(1), tla.int(0))),
        TlaConstDecl("c"),
        TlaVarDecl("v"),
    )

    decls foreach { decl =>
      assert(dec.asTlaDecl(enc(decl)) == decl)
    }

    val modules: Seq[TlaModule] = Seq(
        new TlaModule("Empty", Seq.empty),
        new TlaModule("Module", decls),
    )

    modules foreach { m =>
      assert(dec.asTlaModule(enc(m)) == m)
    }

    assert(dec.fromRoot(enc.makeRoot(modules)) == modules)
  }

  val gens: IrGenerators = new IrGenerators {
    override val maxArgs: Int = 3
  }
  test("Deserializing a serialized IR produces an equivalent IR") {

    // all names are considered constants
    val operators = gens.simpleOperators ++ gens.setOperators ++ gens.logicOperators ++ gens.arithOperators
    val genDecl = gens.genTlaDeclButNotVar(gens.genTlaEx(operators)) _
    val prop = forAll(gens.genTlaModuleWith(genDecl)) { module =>
      val moduleJson = enc(module)
      val moduleFromJson = dec.asTlaModule(moduleJson)

      module =? moduleFromJson
    }
    check(prop, minSuccessful(500), sizeRange(4))
  }

}
