package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.types.TypeVarPool
import at.forsyte.apalache.tla.types.parser.{DefaultType1Parser, Type1Parser}
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

/**
 * Unit tests for translating TLA+ expressions to EtcExpr using rows.
 *
 * @author
 *   Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestToEtcExprRows extends AnyFunSuite with BeforeAndAfterEach with ToEtcExprBase {
  private val parser: Type1Parser = DefaultType1Parser
  private var gen: ToEtcExpr = _

  override protected def beforeEach(): Unit = {
    // a new instance of the translator, as it gives unique names to the variables
    gen = new ToEtcExpr(Map(), TypeAliasSubstitution.empty, new TypeVarPool(), useRows = true)
  }

  test("record set constructor") {
    val funOperType = parser("(Set(a), Set(b)) => Set({ x: a, y: b })")
    val expected = mkConstAppByName(funOperType, "S", "T")
    assert(expected == gen(tla.recSet(tla.str("x"), tla.name("S"), tla.str("y"), tla.name("T"))))
  }

  test("invalid field in record set construction") {
    val invalid = "invalidName"
    val exn = intercept[IllegalArgumentException](
        // record sets expect ValEx(TlaStr(_)), whereas we pass NameEx(_)
        gen(tla.recSet(tla.name(invalid), tla.str("x")))
    )
    assert(exn.getMessage.contains(invalid))
  }

  test("[f1 |-> TRUE, f2 |-> 1]") {
    // here we have simply the record type
    val funOperType = parser("(a, b) => { f1: a, f2: b }")
    val expected = mkConstAppByType(funOperType, BoolT1, IntT1)
    val rec = tla.enumFun(tla.str("f1"), tla.bool(true), tla.str("f2"), tla.int(1))
    assert(expected == gen(rec))
  }

  test("""f["foo"]""") {
    // either a function, or a record
    val funOrReq = Seq(parser("((Str -> a), Str) => a"), parser("({ foo: a, b }, Str) => a"))
    val expected = mkUniqApp(funOrReq, mkUniqName("f"), mkUniqConst(StrT1))
    val access = tla.appFun(tla.name("f"), tla.str("foo"))
    assert(expected == gen(access))

    // Has custom type error message
    assert(gen(access).explain(List(), List()).isDefined)
  }

  test("DOMAIN f") {
    // DOMAIN is applied to one of the four objects: a function, a sequence, a record, or a sparse tuple
    val types = Seq(parser("(a -> b) => Set(a)"), parser("Seq(c) => Set(Int)"), parser("{ d } => Set(Str)"),
        parser("<||> => Set(Int)"))

    val expected = mkAppByName(types, "f")
    val tuple = tla.dom(tla.name("f"))
    assert(expected == gen(tuple))
  }

  test("record update [ f EXCEPT !['foo'] = e2 ]") {
    // a function or a record
    val ex = tla.except(tla.name("f"), tla.tuple(tla.str("foo")), tla.name("e2"))

    val types = Seq(parser("(Str, a) => (Str -> a)"), parser("(Str, a) => { foo: a, b }"))
    val tower = mkUniqApp(types, mkUniqConst(StrT1), mkUniqName("e2"))
    val expected = mkUniqApp(Seq(parser("(c, c) => c")), mkUniqName("f"), tower)
    assert(expected == gen(ex))
  }
}
