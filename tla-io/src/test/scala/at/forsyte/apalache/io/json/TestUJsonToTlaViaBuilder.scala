package at.forsyte.apalache.io.json

import at.forsyte.apalache.io.json.ujsonimpl.{TlaToUJson, UJsonToTlaViaBuilder}
import at.forsyte.apalache.io.lir.{TlaType1PrinterPredefs, TypeTagPrinter, TypeTagReader}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

/**
 * TODO: Implement generators for well-typed IR, then rewrite as PBT
 */
@RunWith(classOf[JUnitRunner])
class TestUJsonToTlaViaBuilder extends AnyFunSuite with Checkers {
  implicit val reader: TypeTagReader = DefaultTagJsonReader
  implicit val printer: TypeTagPrinter = TlaType1PrinterPredefs.printer

  val dec = new UJsonToTlaViaBuilder(sourceStoreOpt = None)
  val enc = new TlaToUJson(locatorOpt = None)

  test("dec(enc(x)) =?= x") {
    val exs: Seq[TlaEx] = Seq(
        tla.and(tla.name("x", BoolT1), tla.bool(true)),
        tla.ite(tla.name("p", BoolT1), tla.name("A", ConstT1("X")), tla.name("B", ConstT1("X"))),
        tla.letIn(
            tla.appOp(tla.name("A", OperT1(Seq(IntT1), IntT1)), tla.int(1)),
            tla.decl(
                "A",
                tla.plus(tla.name("p", IntT1), tla.int(1)),
                tla.param("p", IntT1),
            ),
        ),
    )

    exs.foreach { ex =>
      val encEx = enc(ex)
      val decEx = dec.asTlaEx(encEx)
      assert(decEx == ex)
    }

    // Typed builder should fail on these, and the exceptions should be rethrown as deserialization exceptions
    val badExs: Seq[TlaEx] = Seq(
        NameEx("a")(Untyped),
        OperEx(TlaArithOper.plus, tla.int(1), tla.name("x", BoolT1))(Typed(IntT1)),
    )

    badExs.foreach { ex =>
      val encEx = enc(ex)
      assertThrows[JsonDeserializationError] {
        dec.asTlaEx(encEx)
      }
    }

    val decls: Seq[TlaDecl] = Seq(
        tla.decl("X", tla.eql(tla.name("a", IntT1), tla.int(1)), tla.param("a", IntT1)),
        TlaAssumeDecl(None, tla.eql(tla.int(1), tla.int(0))),
        TlaConstDecl("c"),
        TlaVarDecl("v"),
    )

    decls.foreach { decl =>
      assert(dec.asTlaDecl(enc(decl)) == decl)
    }

    val modules: Seq[TlaModule] = Seq(
        TlaModule("Empty", Seq.empty),
        TlaModule("Module", decls),
    )

    modules.foreach { m =>
      assert(dec.asTlaModule(enc(m)) == m)
    }

    assert(dec.fromRoot(enc.makeRoot(modules)) == modules)
  }

  test("Predef sets (see #1281)") {
    val sets: Seq[TlaEx] = Seq(
        tla.intSet(),
        tla.natSet(),
        tla.booleanSet(),
        tla.stringSet(),
    )

    sets.foreach { s =>
      assert(dec.asTlaEx(enc(s)) == s)
    }

  }

  // TODO: Uncomment once generated IRs are well-typed
//  test("Deserializing a serialized IR produces an equivalent IR") {
//    val gens: IrGenerators = new IrGenerators {
//      override val maxArgs: Int = 3
//    }
//    val operators =
//      gens.simpleOperators ++ gens.logicOperators ++ gens.arithOperators ++ gens.setOperators ++ gens.functionOperators ++ gens.actionOperators ++ gens.temporalOperators
//    val genDecl = gens.genTlaDeclButNotVar(gens.genTlaEx(operators)) _
//    val prop = forAll(gens.genTlaModuleWith(genDecl)) { module =>
//      val moduleJson = enc(module)
//      val moduleFromJson = dec.asTlaModule(moduleJson)
//
//      module =? moduleFromJson
//    }
//    check(prop, minSuccessful(500), sizeRange(7))
//  }

}
