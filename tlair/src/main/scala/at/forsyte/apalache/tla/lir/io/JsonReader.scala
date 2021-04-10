package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaControlOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values._

import java.lang.NumberFormatException
import scala.collection.immutable.HashMap
import scala.collection.mutable.LinkedHashMap
import at.forsyte.apalache.tla.lir.UntypedPredefs.untyped

/**
 * <p>A reader of TlaEx and TlaModule from JSON, for interoperability with external tools.</p>
 *
 * @author Andrey Kuprianov
 */

object JsonReader {

  def readModule(from: ujson.Readable): TlaModule = {
    parseModule(ujson.read(from))
  }

  def readExpr(from: ujson.Readable): TlaEx = {
    parseJson(ujson.read(from))
  }

  // expect ujson.Value to be an encoding of a module
  def parseModule(v: ujson.Value): TlaModule = {
    // it should be a JSON object
    val m = v.objOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting a module object")
    }
    if (!m.contains("module") || !m.contains("declarations"))
      throw new Exception("incorrect TLA+ JSON: malformed module object")
    new TlaModule(parseStr(m("module")), parseDecls(m("declarations")))
  }

  val unaryOps = JsonWriter.unaryOps.map(_.swap)
  val naryOps = JsonWriter.naryOps.map(_.swap)
  val binaryOps = JsonWriter.binaryOps.map(_.swap)
  val naryPairOps = JsonWriter.naryPairOps.map(_.swap)
  val functionalOps = JsonWriter.functionalOps.map(_.swap)
  val boundedPredOps = JsonWriter.boundedPredOps.map(_.swap)
  val unboundedPredOps = JsonWriter.unboundedPredOps.map(_.swap)
  val stutterOps = JsonWriter.stutterOps.map(_.swap)
  val fairnessOps = JsonWriter.fairnessOps.map(_.swap)
  val otherOps = Set("id", "str", "int", "set", "applyFun", "applyOp", "if", "case", "let")

  val sets = HashMap(
      "BOOLEAN" -> TlaBoolSet,
      "Int" -> TlaIntSet,
      "Nat" -> TlaNatSet,
      "Real" -> TlaRealSet,
      "STRING" -> TlaStrSet
  )

  // parse arbitrary ujson.Value
  def parseJson(v: ujson.Value): TlaEx = {
    v match {
      case ujson.Str(value) => NameEx(value)
      case ujson.Num(value) =>
        try {
          // numbers are floating point in JavaScript. Go through the conversion hell.
          val decimal = BigDecimal(value.toString.toDouble).setScale(0, BigDecimal.RoundingMode.DOWN)
          ValEx(TlaInt(decimal.toBigInt()))
        } catch {
          case e: NumberFormatException =>
            throw new Exception("incorrect TLA+ JSON: " + e.getMessage)
        }
      case ujson.Bool(value) => ValEx(TlaBool(value))
      case ujson.Obj(value)  => parseExpr(value)
      case _                 => throw new Exception("incorrect TLA+ JSON: unexpected input")
    }
  }

  // expect ujson.Value to be an encoding of TLA+ expression object
  def parseExpr(m: LinkedHashMap[String, ujson.Value]): TlaEx = {
    val unary = m.keySet & unaryOps.keySet
    val binary = m.keySet & binaryOps.keySet
    val nary = m.keySet & naryOps.keySet
    val naryPair = m.keySet & naryPairOps.keySet
    val functional = m.keySet & functionalOps.keySet
    val boundedPred = m.keySet & boundedPredOps.keySet
    val unboundedPred = m.keySet & unboundedPredOps.keySet
    val stutter = m.keySet & stutterOps.keySet
    val fairness = m.keySet & fairnessOps.keySet
    val other = m.keySet & otherOps
    val ourKeys = unary.size + binary.size + nary.size + naryPair.size + functional.size +
      +boundedPred.size + unboundedPred.size + stutter.size + fairness.size + other.size
    val expr =
      if (ourKeys < 1)
        throw new Exception("incorrect TLA+ JSON: expected expression, but none found")
      else if (ourKeys > 1)
        throw new Exception("incorrect TLA+ JSON: multiple matching expressions")
      else if (unary.nonEmpty)
        OperEx(unaryOps(unary.head), parseJson(m(unary.head)))
      else if (binary.nonEmpty) {
        if (!m.contains("arg"))
          throw new Exception("incorrect TLA+ JSON: expecting 'arg'")
        OperEx(binaryOps(binary.head), parseJson(m(binary.head)), parseJson(m("arg")))
      } else if (nary.nonEmpty)
        OperEx(naryOps(nary.head), parseArray(m(nary.head)): _*)
      else if (naryPair.nonEmpty) {
        OperEx(naryPairOps(naryPair.head), parsePairs(m(naryPair.head)): _*)
      } else if (functional.nonEmpty) {
        if (!m.contains("where"))
          throw new Exception("incorrect TLA+ JSON: expecting 'where'")
        OperEx(functionalOps(functional.head), parseJson(m(functional.head)) +: parsePairs(m("where")): _*)
      } else if (unboundedPred.nonEmpty) {
        if (!m.contains("that"))
          throw new Exception("incorrect TLA+ JSON: expecting 'that'")
        OperEx(unboundedPredOps(unboundedPred.head), parseJson(m(unboundedPred.head)), parseJson(m("that")))
      } else if (boundedPred.nonEmpty) {
        val nameSet = parsePair(m(boundedPred.head))
        if (!m.contains("that"))
          throw new Exception("incorrect TLA+ JSON: expecting 'that'")
        OperEx(boundedPredOps(boundedPred.head), nameSet(0), nameSet(1), parseJson(m("that")))
      } else if (stutter.nonEmpty) {
        if (!m.contains("vars"))
          throw new Exception("incorrect TLA+ JSON: expecting 'vars'")
        OperEx(stutterOps(stutter.head), parseJson(m(stutter.head)), parseJson(m("vars")))
      } else if (fairness.nonEmpty) {
        if (!m.contains("vars"))
          throw new Exception("incorrect TLA+ JSON: expecting 'vars'")
        OperEx(fairnessOps(fairness.head), parseJson(m("vars")), parseJson(m(fairness.head)))
      } else if (other.nonEmpty) {
        other.head match {
          case "id"  => NameEx(parseStr(m("id")))
          case "str" => ValEx(TlaStr(parseStr(m("str"))))
          case "int" => ValEx(TlaInt(BigInt(parseStr(m("int")))))
          case "set" => {
            val set = parseStr(m("set"))
            if (sets.contains(set))
              ValEx(sets(set))
            else
              throw new Exception("can't parse TLA+ JSON: reference to unknown set")
          }
          case "applyFun" => {
            if (!m.contains("arg"))
              throw new Exception("incorrect TLA+ JSON: expecting 'arg'")
            OperEx(TlaFunOper.app, parseJson(m("applyFun")), parseJson(m("arg")))
          }
          case "applyOp" => {
            if (!m.contains("args"))
              throw new Exception("incorrect TLA+ JSON: expecting 'args'")
            val name = parseStr(m("applyOp"))
            val args = parseArray(m("args"))
            if (name == "recFunRef") {
              if (args.nonEmpty)
                throw new Exception("incorrect TLA+ JSON: found arguments for 'recFunRef'")
              OperEx(TlaFunOper.recFunRef)
            } else
              OperEx(TlaOper.apply, NameEx(name) +: args: _*)
          }
          case "if" => {
            if (!m.contains("then") || !m.contains("else"))
              throw new Exception("incorrect TLA+ JSON: malformed 'if'")
            OperEx(TlaControlOper.ifThenElse, parseJson(m("if")), parseJson(m("then")), parseJson(m("else")))
          }
          case "case" => {
            if (m.contains("other"))
              OperEx(TlaControlOper.caseWithOther, parseJson(m("other")) +: parsePairs(m("case")): _*)
            else
              OperEx(TlaControlOper.caseNoOther, parsePairs(m("case")): _*)
          }
          case "let" => {
            if (!m.contains("body"))
              throw new Exception("incorrect TLA+ JSON: malformed 'let'")
            LetInEx(parseJson(m("body")), parseOperDecls(m("let")): _*)
          }
          case _ =>
            throw new Exception("can't parse TLA+ JSON: unknown JSON key")
        }
      } else
        throw new Exception("can't parse TLA+ JSON: cannot find a known JSON key")
    if (m.contains("label")) {
      val (name, args) = parseLabel(m("label"))
      OperEx(TlaOper.label, (expr +: ValEx(TlaStr(name)) +: args): _*)
    } else
      expr
  }

  // expect ujson.Value to be a string
  def parseStr(v: ujson.Value): String = {
    // it should be a JSON string
    v.strOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting string")
    }
  }

  // expect ujson.Value to be an encoding of TLA+ expression array
  def parseArray(v: ujson.Value): Seq[TlaEx] = {
    // it should be a JSON array
    val arr = v.arrOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting expression array")
    }
    arr.map(parseJson)
  }

  // expect ujson.Value to be an encoding of a set of pairs of expressions
  def parsePairs(v: ujson.Value): Seq[TlaEx] = {
    // it should be a JSON array
    val arr = v.arrOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting array of pairs")
    }
    arr.map(parsePair).flatten
  }

  // expect ujson.Value to be an encoding of a pair of expressions
  def parsePair(v: ujson.Value): Seq[TlaEx] = {
    val m = v.objOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting a key-value object")
    }
    if (!m.contains("key") || !m.contains("value"))
      throw new Exception("incorrect TLA+ JSON: malformed key-value object")
    val key = parseJson(m("key"))
    val value = parseJson(m("value"))
    Seq(key, value)
  }

  // expect ujson.Value to be an encoding of a label
  def parseLabel(v: ujson.Value): (String, Seq[TlaEx]) = {
    // it should be a JSON object
    val m = v.objOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting a label object")
    }
    if (!m.contains("name") || !m.contains("args"))
      throw new Exception("incorrect TLA+ JSON: malformed label")
    val name = parseStr(m("name"))
    val args = parseArray(m("args"))
    (name,
        args.map {
      case NameEx(str) => ValEx(TlaStr(str)) // change back from NameEx to ValEx
      case _           => throw new Exception("incorrect TLA+ JSON: malformed label")
    })
  }

  // expect ujson.Value to be an encoding of TLA+ declarations array
  def parseDecls(v: ujson.Value): Seq[TlaDecl] = {
    // it should be a JSON array
    val arr = v.arrOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting declaration array")
    }
    arr.map(parseDecl)
  }

  def parseDecl(v: ujson.Value): TlaDecl = {
    val m = v.objOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting a declaration object")
    }
    if (m.contains("constant"))
      TlaConstDecl(parseStr(m("constant")))
    else if (m.contains("variable"))
      TlaVarDecl(parseStr(m("variable")))
    else if (m.contains("assume"))
      TlaAssumeDecl(parseJson(m("assume")))
    else if (m.contains("operator")) {
      if (!m.contains("body") || !m.contains("params"))
        throw new Exception("incorrect TLA+ JSON: malformed operator declaration")
      TlaOperDecl(parseStr(m("operator")), parseParams(m("params")).toList, parseJson(m("body")))
    } else
      throw new Exception("incorrect TLA+ JSON: malformed declaration object")
  }

  // expect ujson.Value to be an encoding of TLA+ operator declarations array
  def parseOperDecls(v: ujson.Value): Seq[TlaOperDecl] = {
    // it should be a JSON array
    val arr = v.arrOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting declaration array")
    }
    arr.map(parseOperDecl)
  }

  def parseOperDecl(v: ujson.Value): TlaOperDecl = {
    val m = v.objOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting a declaration object")
    }
    if (!m.contains("operator") || !m.contains("body") || !m.contains("params"))
      throw new Exception("incorrect TLA+ JSON: malformed operator declaration")
    TlaOperDecl(parseStr(m("operator")), parseParams(m("params")).toList, parseJson(m("body")))
  }

  // expect ujson.Value to be an encoding of TLA+ params array
  def parseParams(v: ujson.Value): Seq[OperParam] = {
    // it should be a JSON array
    val arr = v.arrOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting parameter array")
    }
    arr.map(parseParam)
  }

  // expect ujson.Value to be an encoding of a parameter
  def parseParam(v: ujson.Value): OperParam = {
    // it should be a JSON object
    val m = v.objOpt match {
      case Some(value) => value
      case None        => throw new Exception("incorrect TLA+ JSON: expecting a parameter object")
    }
    if (
        !m.contains("name") || m("name").strOpt == None
        || !m.contains("arity") || m("arity").numOpt == None || !m("arity").num.isValidInt
    )
      throw new Exception("incorrect TLA+ JSON: malformed parameter")
    val arity = m("arity").num.toInt
    OperParam(m("name").str, arity)
  }
}
