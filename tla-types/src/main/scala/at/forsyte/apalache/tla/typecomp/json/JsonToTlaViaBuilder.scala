package at.forsyte.apalache.tla.typecomp.json

import at.forsyte.apalache.io.json._
import at.forsyte.apalache.io.lir.TypeTagReader
import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.src.{SourceLocation, SourcePosition, SourceRegion}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.{
  TBuilderContext, TBuilderInstruction, TBuilderInternalState, TBuilderScopeException, TBuilderTypeException,
}

import scala.language.implicitConversions
import scala.util.{Failure, Success, Try}

/**
 * A JsonDecoder, which uses the ScopedBuilder to construct TLA IR
 *
 * TODO: Once package refactoring is done, this should replace io.json.JsonToTla. Currently impossible due to dependency
 * issues.
 *
 * @author
 *   Jure Kukovec
 */
class JsonToTlaViaBuilder[T <: JsonRepresentation](
    scalaFactory: ScalaFactory[T],
    sourceStoreOpt: Option[SourceStore] = None,
  )(implicit typeTagReader: TypeTagReader)
    extends JsonDecoder[T] {
  private def getOrThrow(json: T, fieldName: String): T =
    json.getFieldOpt(fieldName).getOrElse {
      throw new JsonDeserializationError(s"JSON has no field named [$fieldName].")
    }

  // TBuilderInstruction only throws exceptions when build is called on it. To narrow the try-catch cope, if we want to
  // rethrow builder exceptions as JsonDeserializationError, we need to do it wit a custom build.
  implicit private def buildWithRethrow[TT](builderState: TBuilderInternalState[TT]): TT =
    try {
      builderState.run(TBuilderContext.empty)._2
    } catch {
      // rethrow as deserialization error
      case e: TBuilderTypeException =>
        throw new JsonDeserializationError(s"JSON contains ill-typed expressions: ${e.getMessage}", e)
      case e: TBuilderScopeException =>
        throw new JsonDeserializationError(s"JSON contains ill-scoped expressions: ${e.getMessage}", e)
    }

  private def validateTag[TT](tagged: TypeTagged[TT], tag: TypeTag): Unit =
    if (tagged.typeTag != tag)
      throw new JsonDeserializationError(s"$tagged is tagged with $tag, but should have ${tagged.typeTag}.")

  private def asParam(json: T): OperParam = {
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

  private def asTlaValEx(json: T): TBuilderInstruction = {
    val kindField = getOrThrow(json, TlaToJson.kindFieldName)
    val kind = scalaFactory.asStr(kindField)

    kind match {
      case "TlaStr" =>
        val valField = getOrThrow(json, "value")
        val valStr = scalaFactory.asStr(valField)
        tla.str(valStr)
      case "TlaDecimal" =>
        throw new JsonDeserializationError("TlaDecimal is not supported.")
      case "TlaInt" =>
        val valField = getOrThrow(json, "value")
        val bi = valField
          .getFieldOpt("bigInt")
          .map { biField =>
            BigInt(scalaFactory.asStr(biField))
          }
          .getOrElse {
            BigInt(scalaFactory.asInt(valField))
          }
        tla.int(bi)
      case "TlaBool" =>
        val valField = getOrThrow(json, "value")
        val valBool = scalaFactory.asBool(valField)
        tla.bool(valBool)
      case "TlaBoolSet" => tla.booleanSet()
      case "TlaIntSet"  => tla.intSet()
      case "TlaStrSet"  => tla.stringSet()
      case "TlaNatSet"  => tla.natSet()
      case _            => throw new JsonDeserializationError(s"$kind is not a valid TlaValue kind")
    }
  }

  private def getSourceLocationOpt(json: T): Option[SourceLocation] = for {
    sourceObj <- json.getFieldOpt(TlaToJson.sourceFieldName)
    fileName <- sourceObj.getFieldOpt("filename").map(scalaFactory.asStr)
    fromObj <- sourceObj.getFieldOpt("from")
    toObj <- sourceObj.getFieldOpt("to")
    fromLine <- fromObj.getFieldOpt("line").map(scalaFactory.asInt)
    fromCol <- fromObj.getFieldOpt("column").map(scalaFactory.asInt)
    toLine <- toObj.getFieldOpt("line").map(scalaFactory.asInt)
    toCol <- toObj.getFieldOpt("column").map(scalaFactory.asInt)
  } yield SourceLocation(
      fileName,
      SourceRegion(
          SourcePosition(fromLine, fromCol),
          SourcePosition(toLine, toCol),
      ),
  )

  private def setLoc(identifiable: Identifiable, locationOpt: Option[SourceLocation]): Unit =
    sourceStoreOpt.foreach { store =>
      locationOpt.foreach { loc =>
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
    val decls = declObjSeq.map(asTlaDecl)

    TlaModule(name, decls)
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
        val body: TlaEx = asTBuilderInstruction(bodyField)
        validateTag(body, typeTag)
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
        val body = asTBuilderInstruction(bodyField)
        val paramsField = getOrThrow(declJson, "formalParams")
        val paramsObjList = scalaFactory.asSeq(paramsField).toList
        val fParams = paramsObjList.map(asParam)
        val paramTypes = typeTag match {
          case Typed(OperT1(args, _)) =>
            val l1 = args.length
            val l2 = fParams.length
            if (l1 != l2)
              throw new JsonDeserializationError(s"$nameField has arity $l1, but the type has arity $l2.")
            args
          case t => throw new JsonDeserializationError(s"$nameField should have an operator type, found $t.")
        }

        val opDecl: TlaOperDecl = tla.decl(name, body, fParams.zip(paramTypes): _*)

        validateTag(opDecl, typeTag)

        opDecl.isRecursive = isRecursive
        opDecl

      case "TlaAssumeDecl" =>
        val bodyField = getOrThrow(declJson, "body")
        val body = asTBuilderInstruction(bodyField)
        TlaAssumeDecl(body)(typeTag)
      case _ => throw new JsonDeserializationError(s"$kind is not a valid TlaDecl kind")
    }
    setLoc(decl, getSourceLocationOpt(declJson))
    decl
  }

  override def asTlaEx(exJson: T): TlaEx = asTBuilderInstruction(exJson)

  // It's more efficient to operate over TBuilderInstruction for as long as possible, and only build in the end step
  private def asTBuilderInstruction(exJson: T): TBuilderInstruction = {
    val kindField = getOrThrow(exJson, TlaToJson.kindFieldName)
    val kind = scalaFactory.asStr(kindField)
    if (kind == "NullEx")
      throw new JsonDeserializationError("NullEx is not supported.")

    val typeField = getOrThrow(exJson, TlaToJson.typeFieldName)
    val tag = scalaFactory.asStr(typeField)
    val typeTag = typeTagReader(tag)
    val exCmp = kind match {
      case "NameEx" =>
        val nameField = getOrThrow(exJson, "name")
        val name = scalaFactory.asStr(nameField)
        val tt1 = typeTag match {
          case Typed(tt: TlaType1) => tt
          case t                   => throw new JsonDeserializationError(s"Expected TlaType1, found $t.")
        }
        tla.name(name, tt1)
      case "ValEx" =>
        val valueField = getOrThrow(exJson, "value")
        asTlaValEx(valueField)

      case "OperEx" =>
        val operField = getOrThrow(exJson, "oper")
        val operString = scalaFactory.asStr(operField)
        val argsField = getOrThrow(exJson, "args")
        val argsObjSeq = scalaFactory.asSeq(argsField)
        val args = argsObjSeq.map(asTBuilderInstruction)
        BuilderCallByName(operString, typeTag.asTlaType1(), args)

      case "LetInEx" =>
        val bodyField = getOrThrow(exJson, "body")
        val body = asTBuilderInstruction(bodyField)
        val declsField = getOrThrow(exJson, "decls")
        val declsObjSeq = scalaFactory.asSeq(declsField)
        val decls = declsObjSeq.map(asTlaDecl)
        assert(decls.forall { _.isInstanceOf[TlaOperDecl] })
        // narrownig cast + unchecked lift to satisfy the TBuilderInternalState[TlaOperDecl] signature
        val operDecls =
          decls.map { d => tla.uncheckedDecl(d.asInstanceOf[TlaOperDecl]) }
        tla.letIn(body, operDecls: _*)
      case _ => throw new JsonDeserializationError(s"$kind is not a valid TlaEx kind")
    }

    exCmp.map { ex =>
      validateTag(ex, typeTag)
      setLoc(ex, getSourceLocationOpt(exJson))
      ex
    }

  }

  override def fromRoot(rootJson: T): Seq[TlaModule] = {
    val versionField = getOrThrow(rootJson, TlaToJson.versionFieldName)
    val version = scalaFactory.asStr(versionField)
    val current = JsonVersion.current
    if (version != current) {
      throw new JsonDeserializationError(s"JSON version is $version, expected $current.")
    } else {
      val modulesField = getOrThrow(rootJson, "modules")
      scalaFactory.asSeq(modulesField).map(asTlaModule)
    }
  }

  override def fromSingleModule(json: T): Try[TlaModule] = {
    for {
      modules <- Try(fromRoot(json))
      module <- modules match {
        case m +: Nil => Success(m)
        case _        => Failure(new JsonDeserializationError(s"JSON included more than one module"))
      }
    } yield module
  }
}
