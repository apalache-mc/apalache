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
    Obj("except" -> toJson(fun), "where" -> args.map(toJson))
  }

  private def mapWhere(body: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    Obj("map" -> toJson(body), "where" -> args.map(toJson))
  }

  private def boundedPred(tla: String, name: TlaEx, from: TlaEx, pred: TlaEx): ujson.Value = {
    Obj(tla -> Arr(toJson(name), toJson(from)), "that" -> toJson(pred))
  }

  private def unboundedPred(tla: String, name: TlaEx, pred: TlaEx): ujson.Value = {
    Obj(tla -> toJson(name), "that" -> toJson(pred))
  }

  private def ifThenElse(pred: TlaEx, thenEx: TlaEx, elseEx: TlaEx): ujson.Value = {
    Obj("IF" -> toJson(pred), "THEN" -> toJson(thenEx), "ELSE" -> toJson(elseEx))
  }

  private def caseSplit(guardsAndUpdates: Seq[TlaEx]): ujson.Value = {
    Obj("CASE" -> guardsAndUpdates.map(toJson))
  }

  private def caseOther(guardsAndUpdates: Seq[TlaEx], other: TlaEx): ujson.Value = {
    Obj("CASE" -> guardsAndUpdates.map(toJson), "OTHER" -> toJson(other))
  }

  private def actionVars(tla: String, action: TlaEx, vars: TlaEx): ujson.Value = {
    Obj(tla -> toJson(action), "vars" -> toJson(vars))
  }

  private def labeled(label: String, decoratedEx: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    val jsonEx = toJson(decoratedEx)
    jsonEx("label") = Obj("name" -> label, "args" -> args.map(toJson))
    jsonEx
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

      // [ x \in S, y \in T |-> e ]  =>  { "function": "e", "where": [ "x", "S", "y", "T"] }
      case OperEx(TlaFunOper.funDef, fun, keysAndValues@_*) =>
        funWhere(fun, keysAndValues)

      // [f EXCEPT ![i_1] = e_1, ![i_2] = e_2]  =>  { "except": "f", "where": [ "i_1", "e_1", "i_2", "e_2"] }
      case OperEx(TlaFunOper.except, fun, keysAndValues@_*) =>
        exceptWith(fun, keysAndValues)

      // f[e]  =>  { "apply": "f", "to": "e" }
      case OperEx(TlaFunOper.app, funEx, argEx) =>
        applyTo(funEx, argEx)

      // {e: x \in S, y \in T} => {"map":"e","where":["x","S","y","T"]}
      case OperEx(TlaSetOper.map, body, keysAndValues@_*) =>
        mapWhere(body, keysAndValues)

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        ifThenElse(pred, thenEx, elseEx)

      //  {x \in S: P} => {"filter": ["x","S"], "with": "P"}
      //  \E x \in S : P => {"exists": ["x","S"], "with": "P"}
      //  \A x \in S : P => {"forall": ["x","S"], "with": "P"}
      //  CHOOSE x \in S : P => {"CHOOSE": ["x","S"], "with": "P"}
      case OperEx(op@_, name, set, pred) if JsonWriter.boundedPredOps.contains(op)  =>
        boundedPred(JsonWriter.boundedPredOps(op), name, set, pred)

      //  \E x : P => {"exists": "x", "with": "P"}
      //  \A x : P => {"forall": "x", "with": "P"}
      //  CHOOSE x : P => {"CHOOSE": "x", "with": "P"}
      case OperEx(op@_, name, pred) if JsonWriter.unboundedPredOps.contains(op)  =>
        unboundedPred(JsonWriter.unboundedPredOps(op), name, pred)

      case OperEx(TlaControlOper.caseNoOther, guardsAndUpdates@_*) =>
        caseSplit(guardsAndUpdates)

      case OperEx(TlaControlOper.caseWithOther, otherEx, guardsAndUpdates@_*) =>
        caseOther(guardsAndUpdates, otherEx)

      //  [A]_vars
      //  <A>_vars
      case OperEx(op@_, action, vars) if JsonWriter.stutterOps.contains(op)  =>
        actionVars(JsonWriter.stutterOps(op), action, vars)

      //  WF_vars(A)
      //  SF_vars(A)
      case OperEx(op@_, vars, action) if JsonWriter.fairnessOps.contains(op)  =>
        actionVars(JsonWriter.fairnessOps(op), action, vars)

      // a labeled expression L3(a, b) :: 42
      // We model this by just introducing a "label" parameter to the decorated expression
      case expr @ OperEx(oper @ TlaOper.label, decoratedEx, ValEx(TlaStr(name)), args @ _*) =>
        val argNames = args map {
          case ValEx(TlaStr(str)) => NameEx(str) // for a more natural encoding, we change strings to names
          case _ => throw new MalformedTlaError("Malformed expression", expr)
        }
        labeled(name, decoratedEx, argNames)

      /**
       * General handling of unary, binary, and nary operators
       *
       * Unary: op e => { "op": "e" }
       * Others: op [x,y,z] => { "op": ["x", "y"," z"] }
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
    BmcOper.withType -> "<:",
    TlaSetOper.funSet -> "function-set" // TODO: instead of `[ -> ]`
  )

  protected val naryOps: Map[TlaOper, String] = HashMap(
    TlaFunOper.enum -> "record", // TODO: instead of `[ |-> ]`
    TlaFunOper.tuple -> "tuple",  // TODO: instead of `<<>>`
    TlaSetOper.enumSet -> "enum", // TODO: instead of `{}`
    TlaSetOper.recSet -> "record-set", // TODO: instead of `[ : ]`
    TlaSetOper.times -> "times",
    TlaArithOper.sum -> "+",  // TODO: we treat `+` as nary operator: in JSON we do not distinguish plus and sum
    TlaArithOper.prod -> "*", // TODO: we treat `*` as nary operator: in JSON we do not distinguish mult and prod
    TlaBoolOper.and -> "and", // TODO: instead of `/\`
    TlaBoolOper.or -> "or"  // TODO: instead of `\/`
  )

  protected val boundedPredOps: Map[TlaOper, String] = HashMap(
    TlaSetOper.filter -> "filter",
    TlaBoolOper.exists -> "exists",
    TlaBoolOper.forall -> "forall",
    TlaOper.chooseBounded -> "CHOOSE"
  )

  protected val unboundedPredOps: Map[TlaOper, String] = HashMap(
    TlaBoolOper.existsUnbounded -> "exists",
    TlaBoolOper.forallUnbounded -> "forall",
    TlaOper.chooseUnbounded -> "CHOOSE",
    TlaTempOper.EE -> "exists-temporal",
    TlaTempOper.AA -> "forall-temporal"
  )

  protected val stutterOps: Map[TlaOper, String] = HashMap(
    TlaActionOper.stutter -> "stutter",
    TlaActionOper.nostutter -> "nostutter"
  )

  protected val fairnessOps: Map[TlaOper, String] = HashMap(
    TlaTempOper.weakFairness -> "WF",
    TlaTempOper.strongFairness -> "SF"
  )

}
