package at.forsyte.apalache.tla.lir.io

import java.io.{File, FileWriter, PrintWriter}

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, _}
import at.forsyte.apalache.tla.lir.predef._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import ujson._

import scala.collection.immutable.HashMap
/**
 * <p>A formatter of TlaEx and TlaModule to JSON, for interoperability with external tools.</p>
 * @author Andrey Kuprianov
 **/

class JsonWriter(writer: PrintWriter, indent: Int = 2) {

  def write(expr: TlaEx): Unit = {
    writer.write(ujson.write(toJson((0, 0), expr), indent))
  }

  def unary(tla: String, arg: ujson.Value): ujson.Value = {
    Obj("tla" -> tla, "arg" -> arg)
  }

  def binary(tla: String, arg1: ujson.Value, arg2: ujson.Value): ujson.Value = {
    Obj("tla" -> tla, "arg1" -> arg1, "arg2" -> arg2)
  }

  def nary(tla: String, args: ujson.Value*): ujson.Value = {
    Obj("tla" -> tla, "args" -> args)
  }

  def toJson(parentPrecedence: (Int, Int), expr: TlaEx): ujson.Value = {
    expr match {
      case NameEx(x) => unary("name", Str(x))

      case ValEx(TlaStr(str)) => Str(str)
      case ValEx(TlaInt(value)) => unary("int", Str(value.toString))
      case ValEx(TlaBool(b)) => if (b) True else False
      case ValEx(TlaBoolSet) => unary("set", "BOOLEAN")
      case ValEx(TlaIntSet) => unary("set", "Int")
      case ValEx(TlaNatSet) => unary("set", "Nat")
      case ValEx(TlaRealSet) => unary("set", "Real")
      case ValEx(TlaStrSet) => unary("set", "STRING")

      case OperEx(op@_, arg) if JsonWriter.unaryOps.contains(op) =>
        unary(JsonWriter.unaryOps(op), toJson(op.precedence, arg))

      case OperEx(op@_, arg1, arg2) if JsonWriter.binaryOps.contains(op) =>
        Obj(
          "tla" -> JsonWriter.binaryOps(op),
          "arg1" -> toJson(op.precedence, arg1),
          "arg2" -> toJson(op.precedence, arg2)
        )

      case OperEx(op@_, args@_*) if JsonWriter.naryOps.contains(op)  =>
        val argJsons = args.map(toJson(op.precedence, _))
//        nary(JsonWriter.naryOps(op), argJsons)
        Obj("tla" -> JsonWriter.naryOps(op), "args" -> argJsons)

      case _ => True
    }
  }
}

object JsonWriter {
  protected val unaryOps = HashMap(
    TlaActionOper.prime -> "prime", // TODO: should we use `'` or `prime` or something else?
    TlaBoolOper.not -> "~",
    TlaArithOper.uminus -> "-",
    TlaSetOper.union -> "UNION",
    TlaSetOper.powerset -> "SUBSET",
    TlaActionOper.enabled -> "ENABLED",
    TlaActionOper.unchanged -> "UNCHANGED",
    TlaFunOper.domain -> "DOMAIN",
    TlaTempOper.box -> "[]",
    TlaTempOper.diamond -> "<>"
  )

  protected val binaryOps = HashMap(
    TlaOper.eq -> "=",
    TlaOper.ne -> "/=",
    TlaBoolOper.implies -> "=>",
    TlaBoolOper.equiv -> "<=>",
    TlaArithOper.plus -> "+",
    TlaArithOper.minus -> "-",
    TlaArithOper.mult -> "*",
    TlaArithOper.div -> "/",
    TlaArithOper.mod -> "%",
    TlaArithOper.realDiv -> "/.",
    TlaArithOper.exp -> "^",
    TlaArithOper.dotdot -> "..",
    TlaArithOper.lt -> "<",
    TlaArithOper.gt -> ">",
    TlaArithOper.le -> "<=",
    TlaArithOper.ge -> ">=",
    TlaSetOper.in -> "\\in",
    TlaSetOper.notin -> "\\notin",
    TlaSetOper.cap -> "\\cap",
    TlaSetOper.cup -> "\\cup",
    TlaSetOper.setminus -> "\\",
    TlaSetOper.subseteq -> "\\subseteq",
    TlaSetOper.subsetProper -> "\\subset",
    TlaSetOper.supseteq -> "\\supseteq",
    TlaSetOper.supsetProper -> "\\supset",
    TlaActionOper.composition -> "\\cdot",
    TlaTempOper.leadsTo -> "~>",
    TlaTempOper.guarantees -> "-+->",
    TlaSeqOper.concat -> "\\o",
    TlcOper.atat -> "@@",
    TlcOper.colonGreater -> ":>",
    BmcOper.assign -> "<-",
    BmcOper.withType -> "<:"
  )

  protected val naryOps: Map[TlaOper, String] = HashMap(
    TlaSetOper.enumSet -> "enum",
    TlaFunOper.tuple -> "tuple",
    TlaSetOper.times -> "\\X",
    TlaArithOper.sum -> "+",
    TlaArithOper.prod -> "*"
  )
}
