package at.forsyte.apalache.io.json

import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.tla.lir.{TestingPredefs, TlaConstDecl, TlaDecl, TlaEx, TlaVarDecl, TypeTag}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSetOper}
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.io.TypeTagPrinter

@RunWith(classOf[JUnitRunner])
class TestTlaToUJson extends FunSuite with BeforeAndAfterEach with TestingPredefs {

  implicit val ttp: TypeTagPrinter = new TypeTagPrinter {
    override def apply(tag: TypeTag): String = ""
  }
  val enc = new TlaToUJson

  val kindField = TlaToJson.kindFieldName

  def getEncVal(ex: TlaEx): ujson.Value = enc(ex).value
  def getEncVal(decl: TlaDecl): ujson.Value = enc(decl).value

  test("Basic values") {
    val int = tla.int(5).untyped()
    val str = tla.str("abc").untyped()
    val bool = tla.bool(true).untyped()

    val Seq(jsonInt, jsonStr, jsonBool) = Seq(int, str, bool) map {
      getEncVal
    }

    assert(jsonInt(kindField).str == "ValEx")
    assert(jsonInt("value")("value").num == 5)

    assert(jsonStr("value")(kindField).str == "TlaStr")
    assert(jsonStr("value")("value").str == "abc")

    assert(jsonBool("value")("value").bool == true)
  }

  test("TLA+ collections") {
    val set = tla.enumSet(tla.int(1), tla.int(2), tla.int(3)).untyped()
    val tup = tla.tuple(Seq("x", "y", "z") map tla.str: _*).untyped()

    val Seq(jsonSeq, jsonTup) = Seq(set, tup) map {
      getEncVal
    }

    assert(jsonSeq(kindField).str == "OperEx")
    assert(jsonSeq("oper").str == TlaSetOper.enumSet.name)
    assert(jsonSeq("args").arr.size == 3)
    assert(jsonSeq("args")(1) == getEncVal(tla.int(2)))

    assert(jsonTup(kindField).str == "OperEx")
    assert(jsonTup("oper").str == TlaFunOper.tuple.name)
    assert(jsonTup("args").arr.size == 3)
    assert(jsonTup("args")(2) == getEncVal(tla.str("z")))
  }

  test("Let-In") {
    // A(p) == p + 1
    val decl = tla
      .declOp(
          "A",
          tla.plus(n_p, tla.int(1)),
          "p"
      )
      .untypedOperDecl()
    // LET A(p) == p + 1
    //  IN A(0)
    val letInEx = tla.letIn(
        tla.appDecl(decl, tla.int(0)),
        decl
    )

    val letJson = getEncVal(letInEx)

    assert(letJson(kindField).str == "LetInEx")
    assert(letJson("body") == getEncVal(tla.appDecl(decl, tla.int(0))))
    assert(letJson("decls").arr.size == 1)
    assert(letJson("decls")(0) == getEncVal(decl))

  }

  test("Non-operator declarations") {
    val constDecl = TlaConstDecl("C")
    val varDecl = TlaVarDecl("x")

    val constJson = getEncVal(constDecl)
    val varJson = getEncVal(varDecl)

    assert(constJson(kindField).str == "TlaConstDecl")
    assert(constJson("name").str == constDecl.name)

    assert(varJson(kindField).str == "TlaVarDecl")
    assert(varJson("name").str == varDecl.name)
  }

  test("Operator declarations") {
    // T == 1
    val nullary = tla.declOp("T", tla.int(1)).untypedOperDecl()
    // T(p) == p
    val unary = tla.declOp("T", n_p, "p").untypedOperDecl()
    // T(A(_),b) == A(b)
    val higherOrder = tla.declOp("T", tla.appOp(n_A, n_b), ("A", 1), "b").untypedOperDecl()
    // RECURSIVE T(_)
    // T(p) == X(p)
    val recursive = tla.declOp("T", tla.appOp(n_T, n_p), "p").untypedOperDecl()
    recursive.isRecursive = true

    val jsons @ Seq(jsonNullary, jsonUnary, jsonHO, jsonRec) =
      Seq(nullary, unary, higherOrder, recursive) map getEncVal

    assert(jsons.forall { _(kindField).str == "TlaOperDecl" })
    assert(jsons.forall { _("name").str == "T" })

    assert(jsonNullary("formalParams").arr.isEmpty)
    assert(!jsonNullary("isRecursive").bool)

    assert(jsonUnary("formalParams").arr.size == 1)
    assert(jsonUnary("formalParams")(0)(kindField).str == "OperParam")
    assert(jsonUnary("formalParams")(0)("name").str == "p")
    assert(jsonUnary("formalParams")(0)("arity").num == 0)
    assert(!jsonUnary("isRecursive").bool)

    assert(jsonHO("formalParams").arr.size == 2)
    assert(jsonHO("formalParams")(0)(kindField).str == "OperParam")
    assert(jsonHO("formalParams")(0)("name").str == "A")
    assert(jsonHO("formalParams")(0)("arity").num == 1)
    assert(jsonHO("formalParams")(1)(kindField).str == "OperParam")
    assert(jsonHO("formalParams")(1)("name").str == "b")
    assert(jsonHO("formalParams")(1)("arity").num == 0)
    assert(!jsonHO("isRecursive").bool)

    assert(jsonRec("isRecursive").bool)
  }

}
