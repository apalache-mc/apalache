package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values._
import scala.collection.immutable.HashMap
import scala.collection.mutable.LinkedHashMap

/**
 * <p>A reader of TlaEx and TlaModule from JSON, for interoperability with external tools.</p>
 * @author Andrey Kuprianov
 **/

object JsonReader {

  def read(from: ujson.Readable): TlaEx = {
    val json = ujson.read(from)
    parseJson(json)
  }

  val unaryOps = JsonWriter.unaryOps.map(_.swap)
  val naryOps = JsonWriter.naryOps.map(_.swap)
  val functionalOps = JsonWriter.functionalOps.map(_.swap)
  val boundedPredOps = JsonWriter.boundedPredOps.map(_.swap)
  val unboundedPredOps = JsonWriter.unboundedPredOps.map(_.swap)
  val otherOps = Set("str", "int", "set")

  val sets = HashMap(
    "BOOLEAN" -> TlaBoolSet,
    "Int" -> TlaIntSet,
    "Nat" -> TlaNatSet,
    "Real" -> TlaRealSet,
    "STRING" -> TlaStrSet
  )

  // parse arbitrary ujson.Value
  def parseJson(v: ujson.Value): TlaEx = {
    println(v.toString)
    v match {
      case ujson.Str(value) => NameEx(value)
      case ujson.Num(value) =>
        if(value.isValidInt) ValEx(TlaInt(value.toInt))
        else throw new Exception("incorrect TLA+ JSON: wrong number")
      case ujson.Bool(value) => ValEx(TlaBool(value))
      case ujson.Obj(value) => parseExpr(value)
      case _ => throw new Exception("incorrect TLA+ JSON: unexpected input")
    }
  }

  // expect ujson.Value to be an encoding of TLA+ expression
  def parseExpr(m: LinkedHashMap[String, ujson.Value]): TlaEx = {
    val unary = m.keySet & unaryOps.keySet
    val functional = m.keySet & functionalOps.keySet
    val boundedPred = m.keySet & boundedPredOps.keySet
    val unboundedPred = m.keySet & unboundedPredOps.keySet
    val nary = m.keySet & naryOps.keySet
    val other = m.keySet & otherOps
    val ourKeys = unary.size + nary.size + functional.size +
      + boundedPred.size + unboundedPred.size + other.size
    if(ourKeys < 1)
      throw new Exception("incorrect TLA+ JSON: expected expression, but none found")
    else if(ourKeys > 1)
      throw new Exception("incorrect TLA+ JSON: multiple matching expressions")
    else if(unary.nonEmpty)
      OperEx(unaryOps(unary.head), parseJson(m(unary.head)))
    else if(nary.nonEmpty)
      OperEx(naryOps(nary.head), parseArray(m(nary.head)):_*)
    else if(functional.nonEmpty) {
      if(!m.contains("where"))
        throw new Exception("incorrect TLA+ JSON: expecting 'where' clause")
      OperEx(functionalOps(functional.head), parseJson(m(functional.head)) +: parsePairs(m("where")) :_*)
    }
    else if(unboundedPred.nonEmpty) {
      if(!m.contains("that"))
        throw new Exception("incorrect TLA+ JSON: expecting 'that' clause")
      OperEx(unboundedPredOps(unboundedPred.head), parseJson(m(unboundedPred.head)), parseJson(m("that")))
    }
    else if(unboundedPred.nonEmpty) {
      if(!m.contains("that"))
        throw new Exception("incorrect TLA+ JSON: expecting 'that' clause")
      OperEx(unboundedPredOps(unboundedPred.head), parseJson(m(unboundedPred.head)), parseJson(m("that")))
    }
    else if(boundedPred.nonEmpty) {
      val nameSet = parsePair(m(boundedPred.head))
      if(!m.contains("that"))
        throw new Exception("incorrect TLA+ JSON: expecting 'that' clause")
      OperEx(boundedPredOps(boundedPred.head), nameSet(0), nameSet(1), parseJson(m("that")))
    }
    else if(other.nonEmpty) {
      if(other.head == "str")
        ValEx(TlaStr(parseStr(m("str"))))
      else if(other.head == "int")
        ValEx(TlaInt(BigInt(parseStr(m("int")))))
      else if(other.head == "set") {
        val set = parseStr(m("set"))
        if(sets.contains(set))
          ValEx(sets(set))
        else
          throw new Exception("can't parse TLA+ JSON: reference to unknown set")
      }
      else
        throw new Exception("can't parse TLA+ JSON: unknown JSON key")
    }
    else
      throw new Exception("can't parse TLA+ JSON: unknown JSON key")
  }

  // expect ujson.Value to be a string
  def parseStr(v: ujson.Value): String = {
    // it should be a JSON string
    v.strOpt match {
      case Some(value) => value
      case None => throw new Exception("incorrect TLA+ JSON: expecting string")
    }
  }

  // expect ujson.Value to be an encoding of TLA+ expression array
  def parseArray(v: ujson.Value): Seq[TlaEx] = {
    // it should be a JSON array
    val arr = v.arrOpt match {
      case Some(value) => value
      case None => throw new Exception("incorrect TLA+ JSON: expecting expression array")
    }
    arr.map(parseJson)
  }

  // expect ujson.Value to be an encoding of a set of pairs of expressions
  def parsePairs(v: ujson.Value): Seq[TlaEx] = {
    // it should be a JSON array
    val arr = v.arrOpt match {
      case Some(value) => value
      case None => throw new Exception("incorrect TLA+ JSON: expecting array of pairs")
    }
    arr.map(parsePair).flatten
  }

  // expect ujson.Value to be an encoding of a pair of expressions
  def parsePair(v: ujson.Value): Seq[TlaEx] = {
    val pair = parseArray(v)
    if(pair.size != 2)
      throw new Exception("incorrect TLA+ JSON: expecting a pair")
    pair
  }
}

