package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.io.lir.TypeTagPrinter
import at.forsyte.apalache.tla.lir.storage.SourceLocator

/**
 * A semi-abstraction of a json encoder. It is independent of the concrete JsonRepresentation, resp. JsonFactory
 * implementation.
 *
 * Every internal representation object, Class( arg1 = v1, ... ,argN = vN, variadicArgs : T* = args) gets encoded as
 * json in the following way: { "type": "untyped" "kind": "Class", "arg1": enc(v1), ... "argN": enc(vN), "variadicArgs":
 * [ enc(args[0]), ... enc(args[k]) ] }
 *
 * where enc is the encoding.
 *
 * Example: OperEx( TlaArithOper.plus, ValEx( TlaInt(1) ), ValEx(TlaInt(2) ) ) ~~~~~> { "type": "(Int, Int) => Int",
 * "kind": "OperEx", "oper": "+" "args": [ { "type": "Int", "kind": "ValEx", "value": { "kind": TlaInt, "value": 1 } },
 * { "type": "Int", "kind": "ValEx", "value": { "kind": TlaInt, "value": 2 } } ] }
 */
class TlaToJson[T <: JsonRepresentation](
    adapter: ScalaToJsonAdapter[T],
    locatorOpt: Option[SourceLocator] = None,
  )(implicit typeTagPrinter: TypeTagPrinter)
    extends JsonEncoder[T] {
  import TlaToJson._

  implicit def liftString: String => T = adapter.fromStr

  implicit def liftInt: Int => T = adapter.fromInt

  implicit def liftBool: Boolean => T = adapter.fromBool

  /**
   * If a SourceLocator is given, prepare a `sourceFieldName` field, holding a JSON with file & position info, in
   * addition to the given fields.
   */
  private def withOptionalLoc(identifiable: Identifiable)(fields: (String, T)*): T = {
    val locFieldOpt: Option[T] = locatorOpt.map { locator =>
      locator
        .sourceOf(identifiable.ID)
        .map { sourceLoc =>
          adapter.mkObj(
              "filename" -> sourceLoc.filename,
              "from" -> adapter.mkObj(
                  "line" -> sourceLoc.region.start.line,
                  "column" -> sourceLoc.region.start.column,
              ),
              "to" -> adapter.mkObj(
                  "line" -> sourceLoc.region.end.line,
                  "column" -> sourceLoc.region.end.column,
              ),
          )
        }
        .getOrElse {
          "UNKNOWN" // Locator is given, but doesn't know the source
        }
    }
    adapter.mkObj((locFieldOpt.map { sourceFieldName -> _ }) ++: fields: _*)
  }

  override def apply(ex: TlaEx): T = {
    def withLoc(fields: (String, T)*): T = withOptionalLoc(ex)(fields: _*)
    ex match {
      case NameEx(name) =>
        withLoc(
            typeFieldName -> typeTagPrinter(ex.typeTag),
            kindFieldName -> "NameEx",
            "name" -> name,
        )

      case ValEx(value) =>
        val inner = value match {
          case TlaStr(strValue) =>
            adapter.mkObj(
                kindFieldName -> "TlaStr",
                "value" -> strValue,
            )
          case TlaDecimal(decValue) =>
            adapter.mkObj(
                kindFieldName -> "TlaDecimal",
                "value" -> decValue.toString(), // let the parser care when reading
            )
          case TlaInt(bigIntValue) =>
            val intVal: T =
              if (bigIntValue.isValidInt) liftInt(bigIntValue.toInt)
              else adapter.mkObj("bigInt" -> bigIntValue.toString())
            adapter.mkObj(
                kindFieldName -> "TlaInt",
                "value" -> intVal,
            )
          case TlaBool(boolValue) =>
            adapter.mkObj(
                kindFieldName -> "TlaBool",
                "value" -> boolValue,
            )
          case TlaBoolSet =>
            adapter.mkObj(
                kindFieldName -> "TlaBoolSet"
            )
          case TlaIntSet =>
            adapter.mkObj(
                kindFieldName -> "TlaIntSet"
            )
          case TlaStrSet =>
            adapter.mkObj(
                kindFieldName -> "TlaStrSet"
            )
          case TlaNatSet =>
            adapter.mkObj(
                kindFieldName -> "TlaNatSet"
            )
          case _ =>
            // unsupported TlaReal
            adapter.mkObj()
        }
        withLoc(
            typeFieldName -> typeTagPrinter(ex.typeTag),
            kindFieldName -> "ValEx",
            "value" -> inner,
        )

      case OperEx(oper, args @ _*) =>
        val argJsons = args.map(apply)
        withLoc(
            typeFieldName -> typeTagPrinter(ex.typeTag),
            kindFieldName -> "OperEx",
            "oper" -> oper.name,
            "args" -> adapter.fromIterable(argJsons),
        )
      case LetInEx(body, decls @ _*) =>
        val bodyJson = apply(body)
        val declJsons = decls.map(apply)
        withLoc(
            typeFieldName -> typeTagPrinter(ex.typeTag),
            kindFieldName -> "LetInEx",
            "body" -> bodyJson,
            "decls" -> adapter.fromIterable(declJsons),
        )

      case NullEx =>
        adapter.mkObj(kindFieldName -> "NullEx")
    }
  }

  override def apply(decl: TlaDecl): T = {
    def withLoc(fields: (String, T)*): T = withOptionalLoc(decl)(fields: _*)
    decl match {
      case TlaTheoremDecl(name, body) =>
        val bodyJson = apply(body)
        withLoc(
            typeFieldName -> typeTagPrinter(decl.typeTag),
            kindFieldName -> "TlaTheoremDecl",
            "name" -> name,
            "body" -> bodyJson,
        )

      case TlaVarDecl(name) =>
        withLoc(
            typeFieldName -> typeTagPrinter(decl.typeTag),
            kindFieldName -> "TlaVarDecl",
            "name" -> name,
        )

      case TlaConstDecl(name) =>
        withLoc(
            typeFieldName -> typeTagPrinter(decl.typeTag),
            kindFieldName -> "TlaConstDecl",
            "name" -> name,
        )

      case decl @ TlaOperDecl(name, formalParams, body) =>
        val bodyJson = apply(body)
        val paramsJsons = formalParams.map { case OperParam(paramName, arity) =>
          adapter.mkObj(
              kindFieldName -> "OperParam",
              "name" -> paramName,
              "arity" -> arity,
          )
        }
        withLoc(
            typeFieldName -> typeTagPrinter(decl.typeTag),
            kindFieldName -> "TlaOperDecl",
            "name" -> name,
            "formalParams" -> adapter.fromIterable(paramsJsons),
            "isRecursive" -> decl.isRecursive,
            "body" -> bodyJson,
        )

      case TlaAssumeDecl(definedName, body) =>
        val bodyJson = apply(body)

        val optionalName: Option[(String, T)] = definedName.map("name" -> _)
        val fields = Seq[(String, T)](
            typeFieldName -> typeTagPrinter(decl.typeTag),
            kindFieldName -> "TlaAssumeDecl",
            "body" -> bodyJson,
        ) ++ optionalName

        withLoc(fields: _*)
    }
  }

  override def apply(module: TlaModule): T = {
    val declJsons = module.declarations.map(apply)
    adapter.mkObj(
        kindFieldName -> "TlaModule",
        "name" -> module.name,
        "declarations" -> adapter.fromIterable(declJsons),
    )
  }

  override def makeRoot(modules: Iterable[TlaModule]): T = {
    val moduleJsons = modules.map(apply)
    adapter.mkObj(
        "name" -> "ApalacheIR",
        versionFieldName -> JsonVersion.current,
        "description" -> "https://apalache-mc.org/docs/adr/005adr-json.html",
        "modules" -> adapter.fromIterable(moduleJsons),
    )
  }
}

object TlaToJson {
  val kindFieldName: String = "kind"
  val typeFieldName: String = "type"
  val sourceFieldName: String = "source"
  val versionFieldName: String = "version"
}
