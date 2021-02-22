package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaDecimal, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir._

object TlaToUJson extends JsonEncoder[UJsonRep] {
  val typeFieldName: String = "type"

  implicit def lift(value: ujson.Value): UJsonRep = UJsonRep(value)

  override def apply(ex: TlaEx): UJsonRep = ex match {
    case NameEx(name) =>
      ujson.Obj(
          typeFieldName -> "NameEx",
          "name" -> name
      )

    case ValEx(value) =>
      val inner = value match {
        case TlaStr(strValue) =>
          ujson.Obj(
              typeFieldName -> "TlaStr",
              "value" -> strValue
          )
        case TlaDecimal(decValue) =>
          ujson.Obj(
              typeFieldName -> "TlaDecimal",
              "value" -> decValue.toString() // let the parser care when reading
          )
        case TlaInt(bigIntValue) =>
          val intVal: ujson.Value =
            if (bigIntValue.isValidInt) ujson.Value.JsonableInt(bigIntValue.toInt)
            else ujson.Obj("bigInt" -> bigIntValue.toString())
          ujson.Obj(
              typeFieldName -> "TlaInt",
              "value" -> intVal
          )
        case TlaBool(boolValue) =>
          ujson.Obj(
              typeFieldName -> "TlaBool",
              "value" -> boolValue
          )
        case _ =>
          //unsupported (TlaReal, TlaPredefSet)
          ujson.Obj()
      }
      ujson.Obj(
          typeFieldName -> "ValEx",
          "value" -> inner
      )

    case OperEx(oper, args @ _*) =>
      val argJsons = args map { arg => apply(arg).value }
      ujson.Obj(
          typeFieldName -> "OperEx",
          "oper" -> oper.name,
          "args" -> ujson.Value.JsonableSeq(argJsons)
      )
    case LetInEx(body, decls @ _*) =>
      val bodyJson = apply(body).value
      val declJsons = decls map { d => apply(d).value }
      ujson.Obj(
          typeFieldName -> "LetInEx",
          "body" -> bodyJson,
          "decls" -> ujson.Value.JsonableSeq(declJsons)
      )

    case NullEx =>
      ujson.Obj(typeFieldName -> "NullEx")
  }

  override def apply(decl: TlaDecl): UJsonRep = decl match {
    case TlaTheoremDecl(name, body) =>
      val bodyJson = apply(body).value
      ujson.Obj(
          typeFieldName -> "TlaTheoremDecl",
          "name" -> name,
          "body" -> bodyJson
      )

    case TlaVarDecl(name) =>
      ujson.Obj(
          typeFieldName -> "TlaVarDecl",
          "name" -> name
      )

    case TlaConstDecl(name) =>
      ujson.Obj(
          typeFieldName -> "TlaConstDecl",
          "name" -> name
      )

    case decl @ TlaOperDecl(name, formalParams, body) =>
      val bodyJson = apply(body).value
      val paramsJsons = formalParams map {
        case SimpleFormalParam(paramName) =>
          ujson.Obj(
              typeFieldName -> "SimpleFormalParam",
              "name" -> paramName
          )
        case OperFormalParam(paramName, arity) =>
          ujson.Obj(
              typeFieldName -> "OperFormalParam",
              "name" -> paramName,
              "arity" -> arity
          )
      }
      ujson.Obj(
          typeFieldName -> "TlaOperDecl",
          "name" -> name,
          "formalParams" -> ujson.Value.JsonableSeq(paramsJsons),
          "isRecursive" -> decl.isRecursive
      )

    case TlaAssumeDecl(body) =>
      val bodyJson = apply(body).value
      ujson.Obj(
          typeFieldName -> "TlaAssumeDecl",
          "body" -> bodyJson
      )
  }

  override def apply(module: TlaModule): UJsonRep = {
    val declJsons = module.declarations map { d =>
      apply(d).value
    }
    ujson.Obj(
        typeFieldName -> "TlaModule",
        "declarations" -> ujson.Value.JsonableSeq(declJsons)
    )
  }
}
