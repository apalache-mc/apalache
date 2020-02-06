package at.forsyte.apalache.tla.lir.io

import java.io.{File, FileWriter, PrintWriter}

import at.forsyte.apalache.tla.lir._
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

  private def primitive(tla: String, value: String): ujson.Value = {
    Obj(tla -> value)
  }

  private def unary(tla: String, arg: TlaEx): ujson.Value = {
    Obj(tla -> toJson(arg))
  }

  private def binary(tla: String, arg1: TlaEx, arg2: TlaEx): ujson.Value = {
    Obj(tla -> Arr(toJson(arg1), toJson(arg2)))
  }

  private def nary(tla: String, args: Seq[TlaEx]): ujson.Value = {
    Obj(tla -> args.map(toJson))
  }

  private def applyTo(fun: TlaEx, to: TlaEx): ujson.Value = {
    Obj("apply" -> toJson(fun), "to" -> toJson(to))
  }

  private def funWhere(fun: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    Obj("function" -> toJson(fun), "where" -> args.map(toJson))
  }

  private def exceptWith(fun: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    Obj("except" -> toJson(fun), "with" -> args.map(toJson))
  }

  def toJson(expr: TlaEx): ujson.Value = {
    expr match {
      /**
       * as name references happen in TLA+ much more frequently than string literals,
       * we optimize for that case, and encode TLA+ name references as JSON strings,
       * while TLA+ strings as { "str" = "..." } JSON objects.
       */
      case NameEx(x) => x
      case ValEx(TlaStr(str)) => primitive("str", str)
      case ValEx(TlaInt(value)) => primitive("int", value.toString)
      case ValEx(TlaBool(b)) => if (b) True else False
      case ValEx(TlaBoolSet) => primitive("set", "BOOLEAN")
      case ValEx(TlaIntSet) => primitive("set", "Int")
      case ValEx(TlaNatSet) => primitive("set", "Nat")
      case ValEx(TlaRealSet) => primitive("set", "Real")
      case ValEx(TlaStrSet) => primitive("set", "STRING")

      /**
       * Introducing special forms for function definitions and applications seems reasonable:
       * again, they occur so frequently, that they deserve a special treatment to improve readability.
       * These forms are:
       *    [ x \in S, y \in T |-> e ] =>
       *    { "function": "e", "where": [ "x", "S", "y", "T"] }
       *
       *    [f EXCEPT ![i_1] = e_1, ![i_2] = e_2] =>
       *    { "except": "f", "with": [ "i_1", "e_1", "i_2", "e_2"] }
       *
       *    f[e] =>
       *    { "apply": "f", "to": "e" }
       */
      case OperEx(TlaFunOper.funDef, fun, keysAndValues@_*) =>
        funWhere(fun, keysAndValues)

      case OperEx(TlaFunOper.except, fun, keysAndValues@_*) =>
        exceptWith(fun, keysAndValues)

      case OperEx(TlaFunOper.app, funEx, argEx) =>
        applyTo(funEx, argEx)

      /**
       * General handling of unary, binary, and nary operators
       *
       * Unary: op e => { "op": "e" }
       * Others:
       */

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
    TlaActionOper.prime -> "prime", // TODO: instead of `'`
    TlaBoolOper.not -> "not",
    TlaArithOper.uminus -> "minus", // TODO: instead of `-` for disambiguation from binary operator
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
    TlaArithOper.plus -> "+", // TODO: we treat `+` as nary operator: in JSON we do not distinguish plus and sum
    TlaArithOper.minus -> "-",
    TlaArithOper.mult -> "*", // TODO: we treat `*` as nary operator: in JSON we do not distinguish mult and prod
    TlaArithOper.div -> "/",
    TlaArithOper.mod -> "%",
    TlaArithOper.realDiv -> "/.",
    TlaArithOper.exp -> "^",
    TlaArithOper.dotdot -> "..",
    TlaArithOper.lt -> "<",
    TlaArithOper.gt -> ">",
    TlaArithOper.le -> "<=",
    TlaArithOper.ge -> ">=",
    TlaSetOper.in -> "in",  // TODO: instead of `\in`
    TlaSetOper.notin -> "notin", // TODO: instead of `\notin`
    TlaSetOper.cap -> "intersect", // TODO: instead of `\cap`
    TlaSetOper.cup -> "union",  // TODO: instead of `\cup`
    TlaSetOper.setminus -> "setminus",  // TODO: instead of `\setminus`
    TlaSetOper.subseteq -> "subseteq",  // TODO: instead of `\subseteq`
    TlaSetOper.subsetProper -> "subset",  // TODO: instead of `\subset`
    TlaSetOper.supseteq -> "supseteq",  // TODO: instead of `\supseteq`
    TlaSetOper.supsetProper -> "supset",  // TODO: instead of `\supset`
    TlaActionOper.composition -> "compose", // TODO: instead of `\cdot`
    TlaTempOper.leadsTo -> "~>",
    TlaTempOper.guarantees -> "-+->",
    TlaSeqOper.concat -> "concat",  // TODO: instead of `\o`
    TlcOper.atat -> "@@",
    TlcOper.colonGreater -> ":>",
    BmcOper.assign -> "<-",
    BmcOper.withType -> "<:"
  )

  protected val naryOps: Map[TlaOper, String] = HashMap(
    TlaSetOper.enumSet -> "enum", // TODO: instead of `{}`
    TlaFunOper.tuple -> "tuple",  // TODO: instead of `<<>>`
    TlaSetOper.times -> "times",
    TlaArithOper.sum -> "+",  // TODO: we treat `+` as nary operator: in JSON we do not distinguish plus and sum
    TlaArithOper.prod -> "*", // TODO: we treat `*` as nary operator: in JSON we do not distinguish mult and prod
    TlaBoolOper.and -> "and", // TODO: instead of `/\`
    TlaBoolOper.or -> "or"  // TODO: instead of `\/`
  )
}
