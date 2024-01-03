package at.forsyte.apalache.io.json

import at.forsyte.apalache.io.json.impl.{DefaultTagReader, TlaToUJson, UJsonToTla}
import at.forsyte.apalache.io.lir.{TlaType1PrinterPredefs, TypeTagReader}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaIntSet, TlaNatSet, TlaStrSet}
import org.junit.runner.RunWith
import org.scalacheck.Prop.{forAll, AnyOperators}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestUJsonToTla extends AnyFunSuite with Checkers {
  import TlaType1PrinterPredefs._
  implicit val reader: TypeTagReader = DefaultTagReader

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
              .withTag(Untyped)
              .asInstanceOf[TlaOperDecl],
        ),
    )

    exs.foreach { ex =>
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

    decls.foreach { decl =>
      assert(dec.asTlaDecl(enc(decl)) == decl)
    }

    val modules: Seq[TlaModule] = Seq(
        new TlaModule("Empty", Seq.empty),
        new TlaModule("Module", decls),
    )

    modules.foreach { m =>
      assert(dec.asTlaModule(enc(m)) == m)
    }

    assert(dec.fromRoot(enc.makeRoot(modules)) == modules)
  }

  test("Predef sets (see #1281)") {
    val sets: Seq[ValEx] = Seq(
        TlaIntSet,
        TlaNatSet,
        TlaBoolSet,
        TlaStrSet,
    ).map { v =>
      ValEx(v).withTag(Untyped)
    }

    sets.foreach { s =>
      assert(dec.asTlaEx(enc(s)) == s)
    }

  }

  test("TypeReader correctly reads valid type strings and fails on invalid type strings") {
    val valid: Seq[String] = Seq(
        "Untyped",
        "Int",
        "Set(Bool)",
        "() => a -> b",
        "(UT, Int) => [x: Str]",
    )

    val invalid: Seq[String] = Seq(
        "",
        "SomeType",
        "Untyped()",
        "-12",
        "Set(true)",
        "() > a -> b",
        "(UT, Int) => [x: 9]",
        "Typed[Str](\"cake\")",
    )

    // No throw
    valid.foreach { s =>
      DefaultTagReader.apply(s)
    }
    invalid.foreach { s =>
      assertThrows[JsonDeserializationError] {
        DefaultTagReader.apply(s)
      }
    }

  }

  test("Deserializing a serialized IR produces an equivalent IR") {
    val gens: IrGenerators = new IrGenerators {
      override val maxArgs: Int = 3
    }
    val operators =
      gens.simpleOperators ++ gens.logicOperators ++ gens.arithOperators ++ gens.setOperators ++ gens.functionOperators ++ gens.actionOperators ++ gens.temporalOperators
    val genDecl = gens.genTlaDeclButNotVar(gens.genTlaEx(operators)) _
    val prop = forAll(gens.genTlaModuleWith(genDecl)) { module =>
      val moduleJson = enc(module)
      val moduleFromJson = dec.asTlaModule(moduleJson)

      module =? moduleFromJson
    }
    check(prop, minSuccessful(500), sizeRange(7))
  }

}
