package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaDecimal, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir._

/**
 * A semi-abstraction of a json encoder.
 * It is independent of the concrete JsonRepresentation, resp. JsonFactory implementation.
 *
 * Every internal representation object, Class( arg1 = v1, ... ,argN = vN, otherArgs = args) gets encoded as json in the following way:
 * {
 *   "type": "Class",
 *   "arg1": enc(v1),
 *   ...
 *   "argN": enc(vN),
 *  "otherArgs": [
 *    enc(args[0]),
 *    ...
 *    enc(args[k])
 *  ]
 * }
 *
 * where enc is the encoding.
 *
 * Example:
 *  OperEx( TlaArithOper.plus, ValEx( TlaInt(1) ), ValEx(TlaInt(2) ) ) ~~~~~>
 *  {
 *    "type": "OperEx",
 *    "oper": "+"
 *    "args": [
 *      {
 *      "type": "ValEx",
 *      "Value": {
 *       "type": TlaInt,
 *       "value": 1
 *        }
 *      },
 *      {
 *      "type": "ValEx",
 *      "Value": {
 *       "type": TlaInt,
 *       "value": 2
 *        }
 *      }
 *    ]
 *  }
 *
 * @param factory A json factory for the `T` variant of JsonRepresentation
 * @tparam T Any class extending JsonRepresentation
 */
class TlaToJson[T <: JsonRepresentation](factory: JsonFactory[T]) extends JsonEncoder[T] {
  val typeFieldName: String = "type"

  implicit def liftString: String => T = factory.fromStr
  implicit def liftInt: Int => T = factory.fromInt
  implicit def liftBool: Boolean => T = factory.fromBool

  override def apply(ex: TlaEx): T = ex match {
    case NameEx(name) =>
      factory.mkObj(
          typeFieldName -> "NameEx",
          "name" -> name
      )

    case ValEx(value) =>
      val inner = value match {
        case TlaStr(strValue) =>
          factory.mkObj(
              typeFieldName -> "TlaStr",
              "value" -> strValue
          )
        case TlaDecimal(decValue) =>
          factory.mkObj(
              typeFieldName -> "TlaDecimal",
              "value" -> decValue.toString() // let the parser care when reading
          )
        case TlaInt(bigIntValue) =>
          val intVal: T =
            if (bigIntValue.isValidInt) liftInt(bigIntValue.toInt)
            else factory.mkObj("bigInt" -> bigIntValue.toString())
          factory.mkObj(
              typeFieldName -> "TlaInt",
              "value" -> intVal
          )
        case TlaBool(boolValue) =>
          factory.mkObj(
              typeFieldName -> "TlaBool",
              "value" -> boolValue
          )
        case _ =>
          //unsupported (TlaReal, TlaPredefSet)
          factory.mkObj()
      }
      factory.mkObj(
          typeFieldName -> "ValEx",
          "value" -> inner
      )

    case OperEx(oper, args @ _*) =>
      val argJsons = args map apply
      factory.mkObj(
          typeFieldName -> "OperEx",
          "oper" -> oper.name,
          "args" -> factory.fromTraversable(argJsons)
      )
    case LetInEx(body, decls @ _*) =>
      val bodyJson = apply(body)
      val declJsons = decls map apply
      factory.mkObj(
          typeFieldName -> "LetInEx",
          "body" -> bodyJson,
          "decls" -> factory.fromTraversable(declJsons)
      )

    case NullEx =>
      factory.mkObj(typeFieldName -> "NullEx")
  }

  override def apply(decl: TlaDecl): T = decl match {
    case TlaTheoremDecl(name, body) =>
      val bodyJson = apply(body)
      factory.mkObj(
          typeFieldName -> "TlaTheoremDecl",
          "name" -> name,
          "body" -> bodyJson
      )

    case TlaVarDecl(name) =>
      factory.mkObj(
          typeFieldName -> "TlaVarDecl",
          "name" -> name
      )

    case TlaConstDecl(name) =>
      factory.mkObj(
          typeFieldName -> "TlaConstDecl",
          "name" -> name
      )

    case decl @ TlaOperDecl(name, formalParams, body) =>
      val bodyJson = apply(body)
      val paramsJsons = formalParams map {
        case SimpleFormalParam(paramName) =>
          factory.mkObj(
              typeFieldName -> "SimpleFormalParam",
              "name" -> paramName
          )
        case OperFormalParam(paramName, arity) =>
          factory.mkObj(
              typeFieldName -> "OperFormalParam",
              "name" -> paramName,
              "arity" -> arity
          )
      }
      factory.mkObj(
          typeFieldName -> "TlaOperDecl",
          "name" -> name,
          "formalParams" -> factory.fromTraversable(paramsJsons),
          "isRecursive" -> decl.isRecursive
      )

    case TlaAssumeDecl(body) =>
      val bodyJson = apply(body)
      factory.mkObj(
          typeFieldName -> "TlaAssumeDecl",
          "body" -> bodyJson
      )
  }

  override def apply(module: TlaModule): T = {
    val declJsons = module.declarations map { d =>
      apply(d)
    }
    factory.mkObj(
        typeFieldName -> "TlaModule",
        "declarations" -> factory.fromTraversable(declJsons)
    )
  }
}
