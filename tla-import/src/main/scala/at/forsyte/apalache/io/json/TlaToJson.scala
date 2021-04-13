package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaDecimal, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.io.TypeTagPrinter

/**
 * A semi-abstraction of a json encoder.
 * It is independent of the concrete JsonRepresentation, resp. JsonFactory implementation.
 *
 * Every internal representation object, Class( arg1 = v1, ... ,argN = vN, variadicArgs : T* = args) gets encoded as json in the following way:
 * {
 * "type": "untyped"
 *  "kind": "Class",
 *  "arg1": enc(v1),
 *  ...
 *  "argN": enc(vN),
 *  "variadicArgs": [
 *    enc(args[0]),
 *    ...
 *    enc(args[k])
 *    ]
 * }
 *
 * where enc is the encoding.
 *
 * Example:
 * OperEx( TlaArithOper.plus, ValEx( TlaInt(1) ), ValEx(TlaInt(2) ) ) ~~~~~>
 * {
 *  "type": "(Int, Int) => Int",
 *  "kind": "OperEx",
 *  "oper": "+"
 *  "args": [
 *    {
 *    "type": "Int",
 *    "kind": "ValEx",
 *    "value": {
 *      "kind": TlaInt,
 *      "value": 1
 *      }
 *    },
 *    {
 *    "type": "Int",
 *    "kind": "ValEx",
 *    "value": {
 *      "kind": TlaInt,
 *      "value": 2
 *      }
 *    }
 *  ]
 * }
 *
 * @param factory A json factory for the `T` variant of JsonRepresentation
 * @tparam T Any class extending JsonRepresentation
 */
class TlaToJson[T <: JsonRepresentation](factory: JsonFactory[T])(implicit typTagPrinter: TypeTagPrinter)
    extends JsonEncoder[T] {
  val kindFieldName: String = "kind"
  val typeFieldName: String = "type"

  implicit def liftString: String => T = factory.fromStr

  implicit def liftInt: Int => T = factory.fromInt

  implicit def liftBool: Boolean => T = factory.fromBool

  override def apply(ex: TlaEx): T = ex match {
    case NameEx(name) =>
      factory.mkObj(
          typeFieldName -> typTagPrinter(ex.typeTag),
          kindFieldName -> "NameEx",
          "name" -> name
      )

    case ValEx(value) =>
      val inner = value match {
        case TlaStr(strValue) =>
          factory.mkObj(
              kindFieldName -> "TlaStr",
              "value" -> strValue
          )
        case TlaDecimal(decValue) =>
          factory.mkObj(
              kindFieldName -> "TlaDecimal",
              "value" -> decValue.toString() // let the parser care when reading
          )
        case TlaInt(bigIntValue) =>
          val intVal: T =
            if (bigIntValue.isValidInt) liftInt(bigIntValue.toInt)
            else factory.mkObj("bigInt" -> bigIntValue.toString())
          factory.mkObj(
              kindFieldName -> "TlaInt",
              "value" -> intVal
          )
        case TlaBool(boolValue) =>
          factory.mkObj(
              kindFieldName -> "TlaBool",
              "value" -> boolValue
          )
        case _ =>
          //unsupported (TlaReal, TlaPredefSet)
          factory.mkObj()
      }
      factory.mkObj(
          typeFieldName -> typTagPrinter(ex.typeTag),
          kindFieldName -> "ValEx",
          "value" -> inner
      )

    case OperEx(oper, args @ _*) =>
      val argJsons = args map apply
      factory.mkObj(
          typeFieldName -> typTagPrinter(ex.typeTag),
          kindFieldName -> "OperEx",
          "oper" -> oper.name,
          "args" -> factory.fromTraversable(argJsons)
      )
    case LetInEx(body, decls @ _*) =>
      val bodyJson = apply(body)
      val declJsons = decls map apply
      factory.mkObj(
          typeFieldName -> typTagPrinter(ex.typeTag),
          kindFieldName -> "LetInEx",
          "body" -> bodyJson,
          "decls" -> factory.fromTraversable(declJsons)
      )

    case NullEx =>
      factory.mkObj(kindFieldName -> "NullEx")
  }

  override def apply(decl: TlaDecl): T = decl match {
    case TlaTheoremDecl(name, body) =>
      val bodyJson = apply(body)
      factory.mkObj(
          typeFieldName -> typTagPrinter(decl.typeTag),
          kindFieldName -> "TlaTheoremDecl",
          "name" -> name,
          "body" -> bodyJson
      )

    case TlaVarDecl(name) =>
      factory.mkObj(
          typeFieldName -> typTagPrinter(decl.typeTag),
          kindFieldName -> "TlaVarDecl",
          "name" -> name
      )

    case TlaConstDecl(name) =>
      factory.mkObj(
          typeFieldName -> typTagPrinter(decl.typeTag),
          kindFieldName -> "TlaConstDecl",
          "name" -> name
      )

    case decl @ TlaOperDecl(name, formalParams, body) =>
      val bodyJson = apply(body)
      val paramsJsons = formalParams map { case OperParam(paramName, arity) =>
        factory.mkObj(
            kindFieldName -> "OperParam",
            "name" -> paramName,
            "arity" -> arity
        )
      }
      factory.mkObj(
          typeFieldName -> typTagPrinter(decl.typeTag),
          kindFieldName -> "TlaOperDecl",
          "name" -> name,
          "formalParams" -> factory.fromTraversable(paramsJsons),
          "isRecursive" -> decl.isRecursive,
          "body" -> bodyJson
      )

    case TlaAssumeDecl(body) =>
      val bodyJson = apply(body)
      factory.mkObj(
          typeFieldName -> typTagPrinter(decl.typeTag),
          kindFieldName -> "TlaAssumeDecl",
          "body" -> bodyJson
      )
  }

  override def apply(module: TlaModule): T = {
    val declJsons = module.declarations map { d =>
      apply(d)
    }
    factory.mkObj(
        kindFieldName -> "TlaModule",
        "declarations" -> factory.fromTraversable(declJsons)
    )
  }
}
