package at.forsyte.apalache.tla.lir.io

import java.io.{File, FileWriter, PrintWriter}

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import ujson._

import scala.collection.immutable.HashMap
import scala.collection.mutable.ArrayBuffer
/**
 * <p>A formatter of TlaEx and TlaModule to JSON, for interoperability with external tools.</p>
 * @author Andrey Kuprianov
 **/

class JsonWriter(writer: PrintWriter, indent: Int = 2) {

  def write(mod: TlaModule): Unit = {
    writer.write(ujson.write(toJson(mod), indent))
  }

  def write(expr: TlaEx): Unit = {
    writer.write(ujson.write(toJson(expr), indent))
  }

  // various forms of JSON encodings of TLA expressions


  private def id(name: String): ujson.Value = {
    primitive("id", name)
  }

  private def primitive(tla: String, value: String): ujson.Value = {
    Obj(tla -> value)
  }

  private def integer(value: BigInt): ujson.Value = {
    if(value.isValidInt)
      value.toInt
    else
      primitive("int", value.toString)
  }

  private def splitIntoPairs(args: Seq[TlaEx]): ujson.Value = {
    var last: ujson.Value = Null
    val res = new ArrayBuffer[ujson.Value]()
    args.foreach(ex =>
      last match {
        case Null =>
          last = toJson(ex)
        case x =>
          res.append(Arr(x, toJson(ex)))
          last = Null
      }
    )
    Arr(res)
  }

  private def unary(op: String, arg: TlaEx): ujson.Value = {
    Obj(op -> toJson(arg))
  }

  private def binary(op: String, arg1: TlaEx, arg2: TlaEx): ujson.Value = {
    Obj(op -> Arr(toJson(arg1), toJson(arg2)))
  }

  private def nary(op: String, args: Seq[TlaEx]): ujson.Value = {
    Obj(op -> args.map(toJson))
  }

  private def naryPair(op: String, args: Seq[TlaEx]): ujson.Value = {
    Obj(op -> splitIntoPairs(args))
  }

  private def applyTo(fun: TlaEx, to: TlaEx): ujson.Value = {
    Obj("apply-fun" -> toJson(fun), "arg" -> toJson(to))
  }

  private def applyOpTo(op: String, to: Seq[TlaEx]): ujson.Value = {
    val json = Obj("apply-op" -> op)
    if(to.nonEmpty)
      json("args") = to.map(toJson)
    json
  }

  private def funWhere(fun: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    Obj("fun" -> toJson(fun), "where" -> splitIntoPairs(args))
  }

  private def recFunWhere(fun: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    Obj("rec-fun" -> toJson(fun), "where" -> splitIntoPairs(args))
  }

  private def recFunRef(): ujson.Value = {
    applyOpTo("rec-fun-ref", Seq())
  }

  private def exceptWhere(fun: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    Obj("except" -> toJson(fun), "where" -> splitIntoPairs(args))
  }

  private def mapWhere(body: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    Obj("map" -> toJson(body), "where" -> splitIntoPairs(args))
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
    Obj("CASE" -> splitIntoPairs(guardsAndUpdates))
  }

  private def caseOther(guardsAndUpdates: Seq[TlaEx], other: TlaEx): ujson.Value = {
    Obj("CASE" -> splitIntoPairs(guardsAndUpdates), "OTHER" -> toJson(other))
  }

  private def actionVars(tla: String, action: TlaEx, vars: TlaEx): ujson.Value = {
    Obj(tla -> toJson(action), "vars" -> toJson(vars))
  }


  private def decompress(value: ujson.Value): ujson.Value = {
    if (value.isInstanceOf[ujson.Str])
      Obj("id" -> value)
    else if (value.isInstanceOf[ujson.Num])
      Obj("int" -> value.num.toInt.toString)
    else
      value
  }

  private def labeled(label: String, decoratedEx: TlaEx, args: Seq[TlaEx]): ujson.Value = {
    val jsonEx = decompress(toJson(decoratedEx))
    jsonEx("label") = Obj("name" -> label, "args" -> args.map(toJson))
    jsonEx
  }

  private def operFormalParam(name: String, arity: Int): ujson.Value = {
    Obj("name" -> name, "arity" -> arity)
  }

  private def operatorDef(name: String, params: Seq[FormalParam], body: TlaEx): ujson.Value = {
    val jsonOp = Obj("OPERATOR" -> name, "body" -> toJson((body)))
    if(params.nonEmpty) // leave out params if not present
      jsonOp("params") = params.map(toJson)
    jsonOp
  }

  private def letIn(declarations: Seq[TlaDecl], body: TlaEx): ujson.Value = {
    Obj("LET" ->  declarations.map(toJson), "IN" -> toJson(body))
  }

  private def module(name: String, declarations: Seq[TlaDecl]): ujson.Value = {
    Obj("MODULE" -> name, "declarations" -> declarations.map(toJson))
  }

  // Transformation functions for modules, declarations, expressions

  def toJson(mod: TlaModule): ujson.Value = {
    module(mod.name, mod.declarations)
  }

  def toJson(decl: TlaDecl): ujson.Value = {
    decl match {
      case TlaConstDecl(name) =>
        primitive("CONSTANT", name)

      case TlaVarDecl(name) =>
        primitive("VARIABLE", name)

      case TlaAssumeDecl(body) =>
        unary("ASSUME", body)

      case TlaOperDecl(name, params, body) =>
        operatorDef(name, params, body)
    }
  }

  private def toJson(param: FormalParam): ujson.Value = {
    param match {
      case SimpleFormalParam(name) =>
        operFormalParam(name, 0)
      case OperFormalParam(name, arity) =>
        operFormalParam(name, arity)
    }
  }

  // TODO: in LIR, do not see anything about function definitions, as allowed by TLA+ grammar (Andrey)

  def toJson(expr: TlaEx): ujson.Value = {
    expr match {
      /**
       * as name references happen in TLA+ much more frequently than string literals,
       * we optimize for that case, and encode TLA+ name references as JSON strings,
       * while TLA+ strings as { "str" = "..." } JSON objects.
       */
      case NameEx(x) => x
      case ValEx(TlaStr(str)) => primitive("str", str)
      case ValEx(TlaInt(value)) => integer(value)
      case ValEx(TlaBool(b)) => if (b) True else False
      case ValEx(TlaBoolSet) => primitive("set", "BOOLEAN")
      case ValEx(TlaIntSet) => primitive("set", "Int")
      case ValEx(TlaNatSet) => primitive("set", "Nat")
      case ValEx(TlaRealSet) => primitive("set", "Real")
      case ValEx(TlaStrSet) => primitive("set", "STRING")

      // [ x \in S, y \in T |-> e ]  =>  { "fun": "e", "where": [ "x", "S", "y", "T"] }
      case OperEx(TlaFunOper.funDef, fun, keysAndValues@_*) =>
        funWhere(fun, keysAndValues)

      // [x \in S] == e into  { "recFun": "e", "where": [ "x", "S" ] }
      case OperEx(TlaFunOper.recFunDef, fun, keysAndValues@_*) =>
        recFunWhere(fun, keysAndValues)

      case OperEx(TlaFunOper.recFunRef) =>
        recFunRef()

      // [f EXCEPT ![i_1] = e_1, ![i_2] = e_2]  =>  { "except": "f", "where": [ "i_1", "e_1", "i_2", "e_2"] }
      case OperEx(TlaFunOper.except, fun, keysAndValues@_*) =>
        exceptWhere(fun, keysAndValues)

      // f[e]  =>  { "apply": "f", "to": "e" }
      case OperEx(TlaFunOper.app, funEx, argEx) =>
        applyTo(funEx, argEx)

      // f[e]  =>  { "apply": "f", "to": "e" }
      case OperEx(op@TlaOper.apply, NameEx(name), args@_*) =>
        applyOpTo(name, args)

      // {e: x \in S, y \in T} => {"map":"e","where":["x","S","y","T"]}
      case OperEx(TlaSetOper.map, body, keysAndValues@_*) =>
        mapWhere(body, keysAndValues)

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        ifThenElse(pred, thenEx, elseEx)

      //  {x \in S: P} => {"filter": ["x","S"], "that": "P"}
      //  \E x \in S : P => {"exists": ["x","S"], "that": "P"}
      //  \A x \in S : P => {"forall": ["x","S"], "that": "P"}
      //  CHOOSE x \in S : P => {"CHOOSE": ["x","S"], "that": "P"}
      case OperEx(op@_, name, set, pred) if JsonWriter.boundedPredOps.contains(op)  =>
        boundedPred(JsonWriter.boundedPredOps(op), name, set, pred)

      //  \E x : P => {"exists": "x", "that": "P"}
      //  \A x : P => {"forall": "x", "that": "P"}
      //  CHOOSE x : P => {"CHOOSE": "x", "that": "P"}
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

      case LetInEx(body, decls@_*) =>
        letIn(decls, body)




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

      case OperEx(op@_, args@_*) if JsonWriter.naryPairOps.contains(op)  =>
        naryPair(JsonWriter.naryPairOps(op), args)

      case _ => True
    }
  }
}

object JsonWriter {

  /**
   * Write a module to a file (without appending).
   *
   * @param module a TLA module
   * @param outputFile an output file that will be created or overwritten
   */
  def write(module: TlaModule, outputFile: File): Unit = {
    val writer = new PrintWriter(new FileWriter(outputFile, false))
    try {
      new JsonWriter(writer).write(module)
    } finally {
      writer.close()
    }
  }
  protected val unaryOps = HashMap(
    TlaActionOper.prime -> "prime",
    TlaBoolOper.not -> "not",
    TlaArithOper.uminus -> "uminus",
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
    TlaSetOper.in -> "in",
    TlaSetOper.notin -> "notin",
    TlaSetOper.cap -> "intersect",
    TlaSetOper.cup -> "union",
    TlaSetOper.setminus -> "setminus",
    TlaSetOper.subseteq -> "subseteq",
    TlaSetOper.subsetProper -> "subset",
    TlaSetOper.supseteq -> "supseteq",
    TlaSetOper.supsetProper -> "supset",
    TlaActionOper.composition -> "compose",
    TlaTempOper.leadsTo -> "~>",
    TlaTempOper.guarantees -> "-+->",
    TlaSeqOper.concat -> "concat",
    TlcOper.atat -> "@@",
    TlcOper.colonGreater -> ":>",
    BmcOper.assign -> "<-",
    BmcOper.withType -> "<:",
    TlaSetOper.funSet -> "fun-set"
  )

  protected val naryOps: Map[TlaOper, String] = HashMap(
    TlaFunOper.tuple -> "tuple",
    TlaSetOper.enumSet -> "enum",
    TlaSetOper.times -> "times",
    TlaArithOper.sum -> "+",
    TlaArithOper.prod -> "*",
    TlaBoolOper.and -> "and",
    TlaBoolOper.or -> "or"
  )

  protected val naryPairOps: Map[TlaOper, String] = HashMap(
    TlaFunOper.enum -> "record",
    TlaSetOper.recSet -> "rec-set"
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
    TlaTempOper.EE -> "EE",
    TlaTempOper.AA -> "AA"
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
