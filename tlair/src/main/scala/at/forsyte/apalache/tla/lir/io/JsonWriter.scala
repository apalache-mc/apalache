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
    writer.write(ujson.write(toJson(expr), indent))
  }

  // various forms of JSON encodings of TLA expressions
  private def unary(tla: String, arg: TlaEx): ujson.Value = {
    Obj(tla -> toJson(arg))
  }

  private def binary(tla: String, arg1: TlaEx, arg2: TlaEx): ujson.Value = {
    Obj(tla -> Arr(toJson(arg1), toJson(arg2)))
  }

  private def nary(tla: String, args: Seq[TlaEx]): ujson.Value = {
    Obj(tla -> args.map(toJson))
  }

  private def defWithArg(tla: String, defn: TlaEx, arg: TlaEx): ujson.Value = {
    Obj(tla -> toJson(defn), "arg" -> toJson(arg))
  }

  private def defWithArgs(tla: String, defn: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    Obj(tla -> toJson(defn), "args" -> args.map(toJson))
  }

  def toJson(expr: TlaEx): ujson.Value = {
    expr match {
      case NameEx(x) => unary("name", tla.str(x))

      case ValEx(TlaStr(str)) => Str(str)
      case ValEx(TlaInt(value)) => unary("int", tla.str(value.toString))
      case ValEx(TlaBool(b)) => if (b) True else False
      case ValEx(TlaBoolSet) => unary("set", tla.str("BOOLEAN"))
      case ValEx(TlaIntSet) => unary("set", tla.str("Int"))
      case ValEx(TlaNatSet) => unary("set", tla.str("Nat"))
      case ValEx(TlaRealSet) => unary("set", tla.str("Real"))
      case ValEx(TlaStrSet) => unary("set", tla.str("STRING"))

      case OperEx(op@_, fun, keysAndValues@_*) if JsonWriter.funOps.contains(op) =>
        defWithArgs(JsonWriter.funOps(op), fun, keysAndValues)

      case OperEx(TlaFunOper.app, funEx, argEx) =>
        defWithArg("fun-app", funEx, argEx)

      case OperEx(op@_, arg) if JsonWriter.unaryOps.contains(op) =>
        unary(JsonWriter.unaryOps(op), arg)

      case OperEx(op@_, arg1, arg2) if JsonWriter.binaryOps.contains(op) =>
        binary(JsonWriter.binaryOps(op), arg1, arg2)

      case OperEx(op@_, args@_*) if JsonWriter.naryOps.contains(op)  =>
        nary(JsonWriter.naryOps(op), args)

      case _ => True
    }
  }
}

object JsonWriter {
  protected val unaryOps = HashMap(
    TlaActionOper.prime -> "prime", // TODO: should we use `'` or `prime` or something else?
    TlaBoolOper.not -> "~",
    TlaArithOper.uminus -> "uminus", // TODO: a word instead of `-` for disambiguation from binary operator
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
    TlaArithOper.sum -> "sum", // TODO: a word instead of `+` for disambiguation from binary operator
    TlaArithOper.prod -> "prod", // TODO: a word instead of `*` for disambiguation from binary operator
    TlaBoolOper.and -> "/\\",
    TlaBoolOper.or -> "\\/"
  )

  protected val funOps: Map[TlaOper, String] = HashMap(
    TlaFunOper.funDef -> "fun-def",
    TlaFunOper.except -> "fun-except"
  )
}
