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
  val binaryOps = JsonWriter.binaryOps.map(_.swap)
  val naryOps = JsonWriter.naryOps.map(_.swap)

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
    val binary = m.keySet & binaryOps.keySet
    val nary = m.keySet & naryOps.keySet

    if(m.keySet == Set("str"))
      ValEx(TlaStr(parseStr(m("str"))))
    else if(unary.size + binary.size < 1)
      throw new Exception("incorrect TLA+ JSON: expected expression, but none found")
    else if(unary.size + binary.size > 1)
      throw new Exception("incorrect TLA+ JSON: multiple matching expressions")
    else if(unary.nonEmpty)
      OperEx(unaryOps(unary.head), parseJson(m(unary.head)))
    else if(binary.nonEmpty)
      OperEx(binaryOps(binary.head), parseArray(m(binary.head)):_*)
    else if(nary.nonEmpty)
      OperEx(naryOps(nary.head), parseArray(m(nary.head)):_*)
    else
      OperEx(naryOps(nary.head), parseArray(m(nary.head)):_*)
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
}

