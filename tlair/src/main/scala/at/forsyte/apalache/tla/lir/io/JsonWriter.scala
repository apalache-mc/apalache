package at.forsyte.apalache.tla.lir.io

import java.io.PrintWriter

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, _}
import at.forsyte.apalache.tla.lir.predef._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import ujson._
/**
 * <p>A formatter of TlaEx and TlaModule to JSON, for interoperability with external tools.</p>
 * @author Andrey Kuprianov
 **/

class JsonWriter(writer: PrintWriter, indent: Int = 2) {

  def write(expr: TlaEx): Unit = {
    writer.write(ujson.write(toJson((0, 0), expr), indent))
  }

  def obj(tla: String, value: ujson.Value = ujson.Null): ujson.Value = {
    Obj("tla" -> tla, "val" -> value)
  }

  def toJson(parentPrecedence: (Int, Int), expr: TlaEx): ujson.Value = {
    expr match {
      case NameEx(x) => obj("name", Str(x))

      case ValEx(TlaStr(str)) => Str(str)
      case ValEx(TlaInt(value)) => obj("int", Str(value.toString))
      case ValEx(TlaBool(b)) => if (b) True else False
      case ValEx(TlaBoolSet) => obj("set", "BOOLEAN")
      case ValEx(TlaIntSet) => obj("set", "Int")
      case ValEx(TlaNatSet) => obj("set", "Nat")
      case ValEx(TlaRealSet) => obj("set", "Real")
      case ValEx(TlaStrSet) => obj("set", "STRING")

      case OperEx(op@TlaActionOper.prime, e) =>
        obj("prime", toJson(op.precedence, e))

      case OperEx(TlaSetOper.enumSet) =>
        // an empty set
        obj("set", Arr())

      case OperEx(op@TlaSetOper.enumSet, arg) =>
        // a singleton set
        obj("set", Arr(toJson(op.precedence, arg)))

      case OperEx(op@TlaSetOper.enumSet, args@_*) =>
        // a set enumeration, e.g., { 1, 2, 3 }
        val argJsons = args.map(toJson(op.precedence, _))
        obj("set", argJsons)

      case OperEx(op@TlaFunOper.tuple, args@_*) =>
        // a tuple, e.g., <<1, 2, 3>>
        val argJsons = args.map(toJson(op.precedence, _))
        obj("tuple", argJsons)

      case _ => True
    }
  }
}