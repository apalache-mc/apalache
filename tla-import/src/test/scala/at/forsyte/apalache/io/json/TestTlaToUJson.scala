package at.forsyte.apalache.io.json

import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.tla.lir.{TestingPredefs, TlaConstDecl, TlaDecl, TlaEx, TlaVarDecl}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSetOper}
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTlaToUJson extends FunSuite with BeforeAndAfterEach with TestingPredefs {
  val enc = TlaToUJson

  val typeField = enc.typeFieldName

  def getEncVal(ex: TlaEx): ujson.Value = enc(ex).value
  def getEncVal(decl: TlaDecl): ujson.Value = enc(decl).value

  test("Basic values") {
    val int = tla.int(5)
    val str = tla.str("abc")
    val bool = tla.bool(true)

    val Seq(jsonInt, jsonStr, jsonBool) = Seq(int, str, bool) map { getEncVal }

    assert(jsonInt(typeField).str == "ValEx")
    assert(jsonInt("value")("value").num == 5)

    assert(jsonStr("value")(typeField).str == "TlaStr")
    assert(jsonStr("value")("value").str == "abc")

    assert(jsonBool("value")("value").bool == true)
  }

  test("TLA+ collections") {
    val set = tla.enumSet(1, 2, 3)
    val tup = tla.tuple(Seq("x", "y", "z") map tla.str: _*)

    val Seq(jsonSeq, jsonTup) = Seq(set, tup) map { getEncVal }

    assert(jsonSeq(typeField).str == "OperEx")
    assert(jsonSeq("oper").str == TlaSetOper.enumSet.name)
    assert(jsonSeq("args").arr.size == 3)
    assert(jsonSeq("args")(1) == getEncVal(tla.int(2)))

    assert(jsonTup(typeField).str == "OperEx")
    assert(jsonTup("oper").str == TlaFunOper.tuple.name)
    assert(jsonTup("args").arr.size == 3)
    assert(jsonTup("args")(2) == getEncVal(tla.str("z")))
  }

  test("Let-In") {
    // A(p) == p + 1
    val decl = tla.declOp(
        "A",
        tla.plus(n_p, 1),
        "p"
    )
    // LET A(p) == p + 1
    //  IN A(0)
    val letInEx = tla.letIn(
        tla.appDecl(decl, 0),
        decl
    )

    val letJson = getEncVal(letInEx)

    assert(letJson(typeField).str == "LetInEx")
    assert(letJson("body") == getEncVal(tla.appDecl(decl, 0)))
    assert(letJson("decls").arr.size == 1)
    assert(letJson("decls")(0) == getEncVal(decl))

  }

  test("Non-operator declarations") {
    val constDecl = TlaConstDecl("C")
    val varDecl = TlaVarDecl("x")

    val constJson = getEncVal(constDecl)
    val varJson = getEncVal(varDecl)

    assert(constJson(typeField).str == "TlaConstDecl")
    assert(constJson("name").str == constDecl.name)

    assert(varJson(typeField).str == "TlaVarDecl")
    assert(varJson("name").str == varDecl.name)
  }

  test("Operator declarations") {
    // T == 1
    val nullary = tla.declOp("T", 1)
    // T(p) == p
    val unary = tla.declOp("T", n_p, "p")
    // T(A(_),b) == A(b)
    val higherOrder = tla.declOp("T", tla.appOp(n_A, n_b), ("A", 1), "b")
    // RECURSIVE T(_)
    // T(p) == X(p)
    val recursive = tla.declOp("T", tla.appOp(n_T, n_p), "p")
    recursive.isRecursive = true

    val jsons @ Seq(jsonNullary, jsonUnary, jsonHO, jsonRec) =
      Seq(nullary, unary, higherOrder, recursive) map getEncVal

    assert(jsons.forall { _(typeField).str == "TlaOperDecl" })
    assert(jsons.forall { _("name").str == "T" })

    assert(jsonNullary("formalParams").arr.isEmpty)
    assert(!jsonNullary("isRecursive").bool)

    assert(jsonUnary("formalParams").arr.size == 1)
    assert(jsonUnary("formalParams")(0)(typeField).str == "SimpleFormalParam")
    assert(jsonUnary("formalParams")(0)("name").str == "p")
    assert(!jsonUnary("isRecursive").bool)

    assert(jsonHO("formalParams").arr.size == 2)
    assert(jsonHO("formalParams")(0)(typeField).str == "OperFormalParam")
    assert(jsonHO("formalParams")(0)("name").str == "A")
    assert(jsonHO("formalParams")(0)("arity").num == 1)
    assert(jsonHO("formalParams")(1)(typeField).str == "SimpleFormalParam")
    assert(jsonHO("formalParams")(1)("name").str == "b")
    assert(!jsonHO("isRecursive").bool)

    assert(jsonRec("isRecursive").bool)
  }

}
