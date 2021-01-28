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
    Readable
  }

  // various forms of JSON encodings of TLA expressions

  private def id(name: String): ujson.Value = {
    primitive("id", name)
  }

  private def primitive(tla: String, value: String): ujson.Value = {
    Obj(tla -> value)
  }

  private def integer(value: BigInt): ujson.Value = {
    if (value.isValidInt)
      value.toInt
    else
      primitive("int", value.toString)
  }

  private def splitIntoPairs(args: Seq[TlaEx]): ujson.Value = {
    var last: ujson.Value = Null
    val res = new ArrayBuffer[ujson.Value]()
    args.foreach(
      ex =>
        last match {
          case Null =>
            last = toJson(ex)
          case x =>
            res.append(Obj("key" -> x, "value" -> toJson(ex)))
            last = Null
        }
    )
    Arr(res)
  }

  private def unary(op: String, arg: TlaEx): ujson.Value = {
    Obj(op -> toJson(arg))
  }

  private def binary(op: String, arg1: TlaEx, arg2: TlaEx): ujson.Value = {
    Obj(op -> toJson(arg1), "arg" -> toJson(arg2))
  }

  private def nary(op: String, args: Seq[TlaEx]): ujson.Value = {
    Obj(op -> args.map(toJson))
  }

  private def naryPair(op: String, args: Seq[TlaEx]): ujson.Value = {
    Obj(op -> splitIntoPairs(args))
  }

  private def applyTo(fun: TlaEx, to: TlaEx): ujson.Value = {
    Obj("applyFun" -> toJson(fun), "arg" -> toJson(to))
  }

  private def applyOpTo(op: String, to: Seq[TlaEx]): ujson.Value = {
    Obj("applyOp" -> op, "args" -> to.map(toJson))
  }

  private def functionalWhere(
      tla: String,
      fun: TlaEx,
      args: Seq[TlaEx]
  ): ujson.Value = {
    Obj(tla -> toJson(fun), "where" -> splitIntoPairs(args))
  }

  private def recFunRef(): ujson.Value = {
    applyOpTo("recFunRef", Seq())
  }

  private def boundedPred(
      tla: String,
      name: TlaEx,
      from: TlaEx,
      pred: TlaEx
  ): ujson.Value = {
    Obj(
      tla -> Obj("key" -> toJson(name), "value" -> toJson(from)),
      "that" -> toJson(pred)
    )
  }

  private def unboundedPred(
      tla: String,
      name: TlaEx,
      pred: TlaEx
  ): ujson.Value = {
    Obj(tla -> toJson(name), "that" -> toJson(pred))
  }

  private def ifThenElse(
      pred: TlaEx,
      thenEx: TlaEx,
      elseEx: TlaEx
  ): ujson.Value = {
    Obj(
      "if" -> toJson(pred),
      "then" -> toJson(thenEx),
      "else" -> toJson(elseEx)
    )
  }

  private def caseSplit(guardsAndUpdates: Seq[TlaEx]): ujson.Value = {
    Obj("case" -> splitIntoPairs(guardsAndUpdates))
  }

  private def caseOther(
      guardsAndUpdates: Seq[TlaEx],
      other: TlaEx
  ): ujson.Value = {
    Obj("case" -> splitIntoPairs(guardsAndUpdates), "other" -> toJson(other))
  }

  private def actionVars(
      tla: String,
      action: TlaEx,
      vars: TlaEx
  ): ujson.Value = {
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

  private def labeled(
      label: String,
      decoratedEx: TlaEx,
      args: Seq[TlaEx]
  ): ujson.Value = {
    val jsonEx = decompress(toJson(decoratedEx))
    jsonEx("label") = Obj("name" -> label, "args" -> args.map(toJson))
    jsonEx
  }

  private def operFormalParam(name: String, arity: Int): ujson.Value = {
    Obj("name" -> name, "arity" -> arity)
  }

  private def operatorDef(
      name: String,
      params: Seq[FormalParam],
      body: TlaEx
  ): ujson.Value = {
    Obj(
      "operator" -> name,
      "body" -> toJson(body),
      "params" -> params.map(toJson)
    )
  }

  private def letIn(declarations: Seq[TlaDecl], body: TlaEx): ujson.Value = {
    Obj("let" -> declarations.map(toJson), "body" -> toJson(body))
  }

  private def module(name: String, declarations: Seq[TlaDecl]): ujson.Value = {
    Obj("module" -> name, "declarations" -> declarations.map(toJson))
  }

  // Transformation functions for modules, declarations, expressions

  def toJson(mod: TlaModule): ujson.Value = {
    module(mod.name, mod.declarations)
  }

  def toJson(decl: TlaDecl): ujson.Value = {
    decl match {
      case TlaConstDecl(name) =>
        primitive("constant", name)

      case TlaVarDecl(name) =>
        primitive("variable", name)

      case TlaAssumeDecl(body) =>
        unary("assume", body)

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
      case NameEx(x)            => x
      case ValEx(TlaStr(str))   => primitive("str", str)
      case ValEx(TlaInt(value)) => integer(value)
      case ValEx(TlaBool(b))    => if (b) True else False
      case ValEx(TlaBoolSet)    => primitive("set", "BOOLEAN")
      case ValEx(TlaIntSet)     => primitive("set", "Int")
      case ValEx(TlaNatSet)     => primitive("set", "Nat")
      case ValEx(TlaRealSet)    => primitive("set", "Real")
      case ValEx(TlaStrSet)     => primitive("set", "STRING")

      case OperEx(op @ _, fun, keysAndValues @ _*)
          if JsonWriter.functionalOps.contains(op) =>
        functionalWhere(JsonWriter.functionalOps(op), fun, keysAndValues)

      case OperEx(TlaFunOper.recFunRef) =>
        recFunRef()

      case OperEx(TlaFunOper.app, funEx, argEx) =>
        applyTo(funEx, argEx)

      case OperEx(op @ TlaOper.apply, NameEx(name), args @ _*) =>
        applyOpTo(name, args)

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        ifThenElse(pred, thenEx, elseEx)

      case OperEx(op @ _, name, set, pred)
          if JsonWriter.boundedPredOps.contains(op) =>
        boundedPred(JsonWriter.boundedPredOps(op), name, set, pred)

      case OperEx(op @ _, name, pred)
          if JsonWriter.unboundedPredOps.contains(op) =>
        unboundedPred(JsonWriter.unboundedPredOps(op), name, pred)

      case OperEx(TlaControlOper.caseNoOther, guardsAndUpdates @ _*) =>
        caseSplit(guardsAndUpdates)

      case OperEx(
          TlaControlOper.caseWithOther,
          otherEx,
          guardsAndUpdates @ _*
          ) =>
        caseOther(guardsAndUpdates, otherEx)

      //  [A]_vars
      //  <A>_vars
      case OperEx(op @ _, action, vars) if JsonWriter.stutterOps.contains(op) =>
        actionVars(JsonWriter.stutterOps(op), action, vars)

      //  WF_vars(A)
      //  SF_vars(A)
      case OperEx(op @ _, vars, action)
          if JsonWriter.fairnessOps.contains(op) =>
        actionVars(JsonWriter.fairnessOps(op), action, vars)

      // a labeled expression L3(a, b) :: 42
      // We model this by just introducing a "label" parameter to the decorated expression
      case expr @ OperEx(
            oper @ TlaOper.label,
            decoratedEx,
            ValEx(TlaStr(name)),
            args @ _*
          ) =>
        val argNames = args map {
          case ValEx(TlaStr(str)) =>
            NameEx(str) // for a more natural encoding, we change strings to names
          case _ => throw new MalformedTlaError("Malformed expression", expr)
        }
        labeled(name, decoratedEx, argNames)

      case LetInEx(body, decls @ _*) =>
        letIn(decls, body)

      /**
        * General handling of unary, binary, and nary operators
        *
        * Unary: op x => { "op": "x" }
        * Binary: op [x,y] => { "op": "x", "arg": "y" }
        * Nary: op [x,y,z] => { "op": ["x", "y"," z"] }
        */
      case OperEx(op @ _, arg) if JsonWriter.unaryOps.contains(op) =>
        unary(JsonWriter.unaryOps(op), arg)

      case OperEx(op @ _, arg1, arg2) if JsonWriter.binaryOps.contains(op) =>
        binary(JsonWriter.binaryOps(op), arg1, arg2)

      case OperEx(op @ _, args @ _*) if JsonWriter.naryOps.contains(op) =>
        nary(JsonWriter.naryOps(op), args)

      case OperEx(op @ _, args @ _*) if JsonWriter.naryPairOps.contains(op) =>
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

  val unaryOps = HashMap(
    TlaActionOper.prime -> "prime",
    TlaBoolOper.not -> "not",
    TlaArithOper.uminus -> "uminus",
    TlaSetOper.union -> "union",
    TlaSetOper.powerset -> "powerset",
    TlaActionOper.enabled -> "enabled",
    TlaActionOper.unchanged -> "unchanged",
    TlaFunOper.domain -> "domain",
    TlaTempOper.box -> "box",
    TlaTempOper.diamond -> "diamond"
  )

  val binaryOps: Map[TlaOper, String] = HashMap(
    TlaOper.eq -> "eq",
    TlaOper.ne -> "ne",
    TlaBoolOper.implies -> "implies",
    TlaBoolOper.equiv -> "equiv",
    TlaArithOper.plus -> "plus",
    TlaArithOper.minus -> "minus",
    TlaArithOper.mult -> "mult",
    TlaArithOper.div -> "div",
    TlaArithOper.mod -> "mod",
    TlaArithOper.realDiv -> "realDiv",
    TlaArithOper.exp -> "exp",
    TlaArithOper.dotdot -> "dotdot",
    TlaArithOper.lt -> "lt",
    TlaArithOper.gt -> "gt",
    TlaArithOper.le -> "le",
    TlaArithOper.ge -> "ge",
    TlaSetOper.in -> "in",
    TlaSetOper.notin -> "notin",
    TlaSetOper.cap -> "cap",
    TlaSetOper.cup -> "cup",
    TlaSetOper.setminus -> "setminus",
    TlaSetOper.subseteq -> "subseteq",
    TlaSetOper.subsetProper -> "subset",
    TlaSetOper.supseteq -> "supseteq",
    TlaSetOper.supsetProper -> "supset",
    TlaActionOper.composition -> "composition",
    TlaTempOper.leadsTo -> "leadsTo",
    TlaTempOper.guarantees -> "guarantees",
    TlaSeqOper.concat -> "concat",
    TlcOper.colonGreater -> "colonGreater",
    BmcOper.assign -> "assign",
    BmcOper.withType -> "lessColon",
    TlaSetOper.funSet -> "funSet"
  )

  val naryOps: Map[TlaOper, String] = HashMap(
    TlcOper.atat -> "atat",
    TlaFunOper.tuple -> "tuple",
    TlaSetOper.enumSet -> "enumSet",
    TlaSetOper.times -> "times",
    TlaBoolOper.and -> "and",
    TlaBoolOper.or -> "or"
  )

  val naryPairOps: Map[TlaOper, String] = HashMap(
    TlaFunOper.enum -> "record",
    TlaSetOper.recSet -> "recSet"
  )

  val boundedPredOps: Map[TlaOper, String] = HashMap(
    TlaSetOper.filter -> "filter",
    TlaBoolOper.exists -> "existsBounded",
    TlaBoolOper.forall -> "forallBounded",
    TlaOper.chooseBounded -> "chooseBounded"
  )

  val unboundedPredOps: Map[TlaOper, String] = HashMap(
    TlaBoolOper.existsUnbounded -> "exists",
    TlaBoolOper.forallUnbounded -> "forall",
    TlaOper.chooseUnbounded -> "choose",
    TlaTempOper.EE -> "EE",
    TlaTempOper.AA -> "AA"
  )

  val functionalOps: Map[TlaOper, String] = HashMap(
    TlaFunOper.funDef -> "funDef",
    TlaFunOper.recFunDef -> "recFunDef",
    TlaFunOper.except -> "except",
    TlaSetOper.map -> "map"
  )

  val stutterOps: Map[TlaOper, String] = HashMap(
    TlaActionOper.stutter -> "stutter",
    TlaActionOper.nostutter -> "nostutter"
  )

  val fairnessOps: Map[TlaOper, String] = HashMap(
    TlaTempOper.weakFairness -> "weakFairness",
    TlaTempOper.strongFairness -> "strongFairness"
  )

}
