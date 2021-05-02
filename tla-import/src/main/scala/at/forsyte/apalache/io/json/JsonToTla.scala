package at.forsyte.apalache.io.json

import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.src.{SourceLocation, SourcePosition, SourceRegion}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaDecimal, TlaInt, TlaStr}
import convenience.tla
import UntypedPredefs._
import at.forsyte.apalache.tla.lir.io.TypeTagReader

/**
 * A semi-abstraction of a json decoder.
 * It is independent of the concrete JsonRepresentation, resp. ScalaFactory implementation.
 * Inverse to TlaToJson, i.e. as{X}( TlaToJson( a : X) ) == a, where X = TlaEx/TlaDecl/TlaModule
 */

class JsonToTla[T <: JsonRepresentation](
    scalaFactory: ScalaFactory[T], sourceStoreOpt: Option[SourceStore] = None
)(implicit typeTagReader: TypeTagReader)
    extends JsonDecoder[T] {

  private def missingField(fieldName: String): JsonDeserializationError =
    new JsonDeserializationError(s"JSON has no field named [$fieldName].")

  private def getOrThrow(json: T, fieldName: String): T =
    json.getFieldOpt(fieldName).getOrElse { throw missingField(fieldName) }

  private def asFParam(json: T): OperParam = {
    val kindField = getOrThrow(json, TlaToJson.kindFieldName)
    val kind = scalaFactory.asStr(kindField)

    kind match {
      case "OperParam" =>
        val nameField = getOrThrow(json, "name")
        val name = scalaFactory.asStr(nameField)
        val arityField = getOrThrow(json, "arity")
        val arity = scalaFactory.asInt(arityField)
        OperParam(name, arity)
      case _ => throw new JsonDeserializationError(s"$kind is not a valid OperParam kind")
    }
  }

  private def asTlaVal(json: T): TlaValue = {
    val kindField = getOrThrow(json, TlaToJson.kindFieldName)
    val kind = scalaFactory.asStr(kindField)

    kind match {
      case "TlaStr" =>
        val valField = getOrThrow(json, "value")
        val valStr = scalaFactory.asStr(valField)
        TlaStr(valStr)
      case "TlaDecimal" =>
        val valField = getOrThrow(json, "value")
        val valStr = scalaFactory.asStr(valField)
        val dec = BigDecimal(valStr)
        TlaDecimal(dec)
      case "TlaInt" =>
        val valField = getOrThrow(json, "value")
        val bi = valField.getFieldOpt("bigInt") map { biField =>
          BigInt(scalaFactory.asStr(biField))
        } getOrElse {
          BigInt(scalaFactory.asInt(valField))
        }
        TlaInt(bi)
      case "TlaBool" =>
        val valField = getOrThrow(json, "value")
        val valBool = scalaFactory.asBool(valField)
        TlaBool(valBool)
      case _ => throw new JsonDeserializationError(s"$kind is not a valid TlaValue kind")
    }
  }

  def getSourceLocationOpt(json: T): Option[SourceLocation] = for {
    sourceObj <- json.getFieldOpt(TlaToJson.sourceFieldName)
    fileName <- sourceObj.getFieldOpt("filename") map scalaFactory.asStr
    fromObj <- sourceObj.getFieldOpt("from")
    toObj <- sourceObj.getFieldOpt("to")
    fromLine <- fromObj.getFieldOpt("line") map scalaFactory.asInt
    fromCol <- fromObj.getFieldOpt("column") map scalaFactory.asInt
    toLine <- toObj.getFieldOpt("line") map scalaFactory.asInt
    toCol <- toObj.getFieldOpt("column") map scalaFactory.asInt
  } yield SourceLocation(
      fileName,
      SourceRegion(
          SourcePosition(fromLine, fromCol),
          SourcePosition(toLine, toCol)
      )
  )

  def setLoc(identifiable: Identifiable, locationOpt: Option[SourceLocation]): Unit =
    sourceStoreOpt foreach { store =>
      locationOpt foreach { loc =>
        store.add(identifiable.ID, loc)
      }
    }

  override def asTlaModule(moduleJson: T): TlaModule = {
    val kindField = getOrThrow(moduleJson, TlaToJson.kindFieldName)
    val kind = scalaFactory.asStr(kindField)
    if (kind != "TlaModule")
      throw new JsonDeserializationError(s"JSON kind is $kind, expected TlaModule")

    val nameField = getOrThrow(moduleJson, "name")
    val name = scalaFactory.asStr(nameField)
    val declField = getOrThrow(moduleJson, "declarations")
    val declObjSeq = scalaFactory.asSeq(declField)
    val decls = declObjSeq map asTlaDecl

    new TlaModule(name, decls)
  }

  override def asTlaDecl(declJson: T): TlaDecl = {
    val typeField = getOrThrow(declJson, TlaToJson.typeFieldName)
    val tag = scalaFactory.asStr(typeField)
    val typeTag = typeTagReader(tag)
    val kindField = getOrThrow(declJson, TlaToJson.kindFieldName)
    val kind = scalaFactory.asStr(kindField)
    val decl = kind match {
      case "TlaTheoremDecl" =>
        val nameField = getOrThrow(declJson, "name")
        val name = scalaFactory.asStr(nameField)
        val bodyField = getOrThrow(declJson, "body")
        val body = asTlaEx(bodyField)
        TlaTheoremDecl(name, body)(typeTag)
      case "TlaVarDecl" =>
        val nameField = getOrThrow(declJson, "name")
        val name = scalaFactory.asStr(nameField)
        TlaVarDecl(name)(typeTag)
      case "TlaConstDecl" =>
        val nameField = getOrThrow(declJson, "name")
        val name = scalaFactory.asStr(nameField)
        TlaConstDecl(name)(typeTag)
      case "TlaOperDecl" =>
        val nameField = getOrThrow(declJson, "name")
        val name = scalaFactory.asStr(nameField)
        val recField = getOrThrow(declJson, "isRecursive")
        val isRecursive = scalaFactory.asBool(recField)
        val bodyField = getOrThrow(declJson, "body")
        val body = asTlaEx(bodyField)
        val paramsField = getOrThrow(declJson, "formalParams")
        val paramsObjList = scalaFactory.asSeq(paramsField).toList
        val fParams = paramsObjList map asFParam
        val opDecl = TlaOperDecl(name, fParams, body)(typeTag)
        opDecl.isRecursive = isRecursive
        opDecl

      case "TlaAssumeDecl" =>
        val bodyField = getOrThrow(declJson, "body")
        val body = asTlaEx(bodyField)
        TlaAssumeDecl(body)(typeTag)
      case _ => throw new JsonDeserializationError(s"$kind is not a valid TlaDecl kind")
    }
    setLoc(decl, getSourceLocationOpt(declJson))
    decl
  }

  override def asTlaEx(exJson: T): TlaEx = {
    val kindField = getOrThrow(exJson, TlaToJson.kindFieldName)
    val kind = scalaFactory.asStr(kindField)
    if (kind == "NullEx") NullEx // TODO: We really shouldn't support NullEx long-term
    val typeField = getOrThrow(exJson, TlaToJson.typeFieldName)
    val tag = scalaFactory.asStr(typeField)
    val typeTag = typeTagReader(tag)
    val ex = kind match {
      case "NameEx" =>
        val nameField = getOrThrow(exJson, "name")
        val name = scalaFactory.asStr(nameField)
        NameEx(name)(typeTag)
      case "ValEx" =>
        val valueField = getOrThrow(exJson, "value")
        val value = asTlaVal(valueField)
        ValEx(value)(typeTag)
      case "OperEx" =>
        val operField = getOrThrow(exJson, "oper")
        val operString = scalaFactory.asStr(operField)
        val argsField = getOrThrow(exJson, "args")
        val argsObjSeq = scalaFactory.asSeq(argsField)
        // TODO: Implement a oper.name -> oper mapping and avoid Builder hackery
        val args = argsObjSeq map asTlaEx map { BuilderTlaExWrapper }
        tla.byName(operString, args: _*).withTag(typeTag)
      case "LetInEx" =>
        val bodyField = getOrThrow(exJson, "body")
        val body = asTlaEx(bodyField)
        val declsField = getOrThrow(exJson, "decls")
        val declsObjSeq = scalaFactory.asSeq(declsField)
        val decls = declsObjSeq map asTlaDecl
        assert(decls forall { _.isInstanceOf[TlaOperDecl] })
        val operDecls = decls map { _.asInstanceOf[TlaOperDecl] }
        LetInEx(body, operDecls: _*)(typeTag)
      case _ => throw new JsonDeserializationError(s"$kind is not a valid TlaEx kind")
    }
    setLoc(ex, getSourceLocationOpt(exJson))
    ex
  }

  override def fromRoot(rootJson: T): Seq[TlaModule] = {
    val versionField = getOrThrow(rootJson, TlaToJson.versionFieldName)
    val version = scalaFactory.asStr(versionField)
    val current = JsonVersion.current
    if (version != current)
      throw new JsonDeserializationError(s"JSON version is $version, expected $current.")

    val modulesField = getOrThrow(rootJson, "modules")
    val modulesObjSeq = scalaFactory.asSeq(modulesField)

    modulesObjSeq map asTlaModule
  }
}
