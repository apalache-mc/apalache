package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.tla.lir.Feature
import com.fasterxml.jackson.core.{JsonFactory, JsonParser}
import com.fasterxml.jackson.databind.node.ObjectNode
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}

import java.nio.file.{InvalidPathException, Path}

import scala.collection.mutable.ListBuffer
import scala.jdk.CollectionConverters._

/**
 * Strict JSON parser and writer for sparse `ApalacheConfig` values.
 *
 * [[parse]] parses and checks one JSON document; [[write]] emits canonical JSON without applying source precedence,
 * runtime defaults, or mode-specific validation. A request-local `JsonDecoder` maps JSON fields and sections to patch
 * classes while accumulating all actionable errors and migration warnings. The `decode*` and `write*` methods handle
 * top-level structures; the remaining helpers handle leaf values.
 *
 * The package model and maintenance rules are documented in the
 * [[https://github.com/apalache-mc/apalache/blob/main/tla-io/src/main/scala/at/forsyte/apalache/io/config/README.md package README]].
 */
object ApalacheConfigJsonParser {
  private val factory = new JsonFactory()
  factory.enable(JsonParser.Feature.STRICT_DUPLICATE_DETECTION)
  private val mapper = new ObjectMapper(factory)

  /** Parse one strict JSON document into a sparse configuration, using `sourceName` to identify diagnostics. */
  def parse(
      sourceText: String,
      sourceName: String = "<configuration>"): ConfigParseResult[ApalacheConfig] = {
    val errors = ListBuffer.empty[String]
    val warnings = ListBuffer.empty[String]
    val root =
      try {
        val parser = mapper.createParser(sourceText)
        try {
          val value = mapper.readTree[JsonNode](parser)
          if (value == null) {
            errors += s"$sourceName: Expected a JSON object, but the document is empty."
          }
          if (parser.nextToken() != null) {
            errors += s"$sourceName: Trailing content after the JSON document is not allowed."
          }
          value
        } finally {
          parser.close()
        }
      } catch {
        case e: Exception =>
          errors += s"$sourceName: Invalid strict JSON: ${e.getMessage}"
          null
      }

    if (root == null || errors.nonEmpty) {
      return ConfigParseResult.failure(errors.toList, warnings.toList)
    }
    if (!root.isObject) {
      return ConfigParseResult.failure(
          List(s"$sourceName: Expected the configuration root to be a JSON object."),
          warnings.toList,
      )
    }

    val decoder = new JsonDecoder(errors, warnings)
    val config = decoder.config(root.asInstanceOf[ObjectNode])
    if (errors.isEmpty) ConfigParseResult.success(config, warnings.toList)
    else ConfigParseResult.failure(errors.toList, warnings.toList)
  }

  /** Serialize the fields present in `config`, optionally with pretty-printing. */
  def write(config: ApalacheConfig, usePrettyPrinter: Boolean = false): String = {
    val root = mapper.createObjectNode()
    writeTopLevelOptions(root, config)
    writeChecker(root, config.checker)
    writeTypechecker(root, config.typechecker)
    writeTrace(root, config.traceEvaluation)
    writeServer(root, config.server)
    if (usePrettyPrinter) mapper.writerWithDefaultPrettyPrinter().writeValueAsString(root)
    else mapper.writeValueAsString(root)
  }

  /** Per-decode state that translates JSON nodes while collecting errors and warnings. */
  final private class JsonDecoder(
      errors: ListBuffer[String],
      warnings: ListBuffer[String]) {

    /** Decode all recognized top-level keys and sections; malformed values contribute errors to this decoder. */
    def config(root: ObjectNode): ApalacheConfig = {
      rejectUnknown(
          root,
          "$",
          Set(
              "command",
              "config-file",
              "out-dir",
              "run-dir",
              "debug",
              "smtprof",
              "write-intermediate",
              "profiling",
              "features",
              "source",
              "output",
              "checker",
              "typechecker",
              "tracee",
              "server",
          ),
      )
      val (context, common) = decodeTopLevelOptions(root)
      ApalacheConfig(
          context = context,
          common = common,
          source = source(root, "source", "$"),
          output = pathValue(root, "output", "$"),
          checker = decodeChecker(objectField(root, "checker", "$")),
          typechecker = decodeTypechecker(objectField(root, "typechecker", "$")),
          traceEvaluation = decodeTrace(objectField(root, "tracee", "$")),
          server = decodeServer(objectField(root, "server", "$")),
      )
    }

    private def decodeTopLevelOptions(root: ObjectNode): (RunContextPatch, CommonPatch) =
      (
          RunContextPatch(
              command = text(root, "command", "$"),
              configFile = pathValue(root, "config-file", "$"),
          ),
          CommonPatch(
              outDir = pathValue(root, "out-dir", "$"),
              runDir = pathValue(root, "run-dir", "$"),
              debug = boolean(root, "debug", "$"),
              smtprof = boolean(root, "smtprof", "$"),
              writeIntermediate = boolean(root, "write-intermediate", "$"),
              profiling = boolean(root, "profiling", "$"),
              features = featureList(root, "features", "$"),
          ),
      )

    private def decodeChecker(node: Option[ObjectNode]): CheckerPatch =
      node match {
        case None =>
          CheckerPatch()

        case Some(obj) =>
          val path = "$.checker"
          val aliases = Set("timeout-smt-sec", "no-deadlocks", "temporal-props")
          rejectUnknown(
              obj,
              path,
              Set(
                  "tuning",
                  "algo",
                  "config",
                  "discard-disabled",
                  "cinit",
                  "init",
                  "inv",
                  "next",
                  "length",
                  "max-error",
                  "timeout-smt",
                  "no-deadlock",
                  "smt-solver",
                  "smt-encoding",
                  "temporal",
                  "view",
              ) ++ aliases,
          )

          val timeoutNode = aliased(obj, "timeout-smt", Seq("timeout-smt-sec"), path)
          val deadlockNode = aliased(obj, "no-deadlock", Seq("no-deadlocks"), path)
          val temporalNode = aliased(obj, "temporal", Seq("temporal-props"), path)

          CheckerPatch(
              tuning = stringMap(obj, "tuning", path),
              algorithm = enumValue(obj, "algo", path, Algorithm.fromString),
              tlcConfig = pathValue(obj, "config", path),
              discardDisabled = boolean(obj, "discard-disabled", path),
              constantInitializer = text(obj, "cinit", path),
              init = text(obj, "init", path),
              invariants = stringList(obj, "inv", path),
              next = text(obj, "next", path),
              length = integer(obj, "length", path),
              maxError = integer(obj, "max-error", path),
              timeoutSmtSeconds = integerNode(timeoutNode, s"$path.timeout-smt"),
              checkDeadlocks = negate(booleanNode(deadlockNode, s"$path.no-deadlock")),
              smtSolver = enumValue(obj, "smt-solver", path, SMTSolver.fromString),
              smtEncoding = enumValue(obj, "smt-encoding", path, SMTEncoding.fromString),
              temporalProperties = stringListNode(temporalNode, s"$path.temporal"),
              view = text(obj, "view", path),
          )
      }

    private def decodeTypechecker(node: Option[ObjectNode]): TypecheckerPatch =
      node match {
        case None =>
          TypecheckerPatch()
        case Some(obj) =>
          val path = "$.typechecker"
          rejectUnknown(obj, path, Set("infer-poly", "inferpoly"))
          TypecheckerPatch(booleanNode(aliased(obj, "infer-poly", Seq("inferpoly"), path), s"$path.infer-poly"))
      }

    private def decodeTrace(node: Option[ObjectNode]): TraceEvaluationPatch =
      node match {
        case None =>
          TraceEvaluationPatch()
        case Some(obj) =>
          val path = "$.tracee"
          rejectUnknown(obj, path, Set("trace", "expressions"))
          TraceEvaluationPatch(
              trace = source(obj, "trace", path),
              expressions = stringList(obj, "expressions", path),
          )
      }

    private def decodeServer(node: Option[ObjectNode]): ServerPatch =
      node match {
        case None =>
          ServerPatch()
        case Some(obj) =>
          val path = "$.server"
          rejectUnknown(obj, path, Set("port", "server-type"))
          ServerPatch(
              port = integer(obj, "port", path),
              serverType = enumValue(
                  obj,
                  "server-type",
                  path,
                  value => {
                    val normalized = value.stripSuffix("-server")
                    ServerType.fromString(normalized)
                  },
              ),
          )
      }

    // Leaf decoders return None for an absent or invalid value; invalid values also append a diagnostic.
    private def source(obj: ObjectNode, field: String, parent: String): Option[InputSource] = {
      val node = obj.get(field)
      if (node == null) {
        return None
      }

      val path = s"$parent.$field"
      if (node.isTextual) {
        expandedPath(node.textValue(), path) match {
          case Some(sourcePath) => recordSource(InputSource.FileSource(sourcePath), path)
          case None             => None
        }
      } else if (node.isObject) {
        val sourceObj = node.asInstanceOf[ObjectNode]
        rejectUnknown(sourceObj, path, Set("kind", "type", "path", "file", "content", "aux", "format"))
        val kindNode = aliased(sourceObj, "kind", Seq("type"), path)
        val kind =
          kindNode match {
            case Some(value) if value.isTextual =>
              value.textValue().toLowerCase
            case _ if sourceObj.has("content") =>
              "string"
            case _ if sourceObj.has("path") || sourceObj.has("file") =>
              "file"
            case _ =>
              errors += s"$path: Source object requires kind, path, or content."
              ""
          }

        kind match {
          case "file" | "filesource" =>
            val pathNode = aliased(sourceObj, "path", Seq("file"), path)
            val sourcePath = textNode(pathNode, s"$path.path") match {
              case Some(value) => expandedPath(value, s"$path.path")
              case None        => None
            }
            sourcePath match {
              case None =>
                None
              case Some(value) =>
                val format = formatValue(sourceObj.get("format"), s"$path.format")
                format match {
                  case Some(sourceFormat) =>
                    Some(InputSource.FileSource(value, sourceFormat))
                  case None if sourceObj.has("format") =>
                    None
                  case None =>
                    recordSource(InputSource.FileSource(value), path)
                }
            }

          case "string" | "stringsource" =>
            val content = text(sourceObj, "content", path)
            val aux = stringList(sourceObj, "aux", path)
            val format = formatValue(sourceObj.get("format"), s"$path.format")
            if (
                content.nonEmpty && (!sourceObj.has("aux") || aux.nonEmpty) &&
                (!sourceObj.has("format") || format.nonEmpty)
            ) {
              Some(InputSource.StringSource(
                      content.get,
                      aux.getOrElse(Nil),
                      format.getOrElse(InputSource.Format.Tla),
                  ))
            } else {
              None
            }

          case other if other.nonEmpty =>
            errors += s"$path.kind: Expected \"file\" or \"string\", but got \"$other\"."
            None

          case _ =>
            None
        }
      } else {
        errors += s"$path: Expected a path string or source object."
        None
      }
    }

    private def formatValue(node: JsonNode, path: String): Option[InputSource.Format] = {
      if (node == null) {
        return None
      }
      scalarEnumText(node, path) match {
        case Some(value) => convertValue(value, path, InputSource.Format.fromString)
        case None        => None
      }
    }

    private def featureList(obj: ObjectNode, field: String, parent: String): Option[List[Feature]] =
      stringList(obj, field, parent) match {
        case None =>
          None
        case Some(strings) =>
          val features = ListBuffer.empty[Feature]
          strings.foreach { value =>
            Feature.fromString(value) match {
              case Some(feature) => features += feature
              case None          => errors += s"$parent.$field: Unexpected feature: $value"
            }
          }
          if (features.size == strings.size) Some(features.toList) else None
      }

    private def enumValue[A](
        obj: ObjectNode,
        field: String,
        parent: String,
        fromString: String => A): Option[A] = {
      val node = obj.get(field)
      if (node == null) {
        return None
      }
      val path = s"$parent.$field"
      scalarEnumText(node, path) match {
        case Some(value) => convertValue(value, path, fromString)
        case None        => None
      }
    }

    /** Converts an enum-like value and records a path-qualified conversion error. */
    private def convertValue[A](value: String, path: String, fromString: String => A): Option[A] =
      try {
        Some(fromString(value))
      } catch {
        case e: IllegalArgumentException =>
          errors += s"$path: ${e.getMessage}"
          None
      }

    private def scalarEnumText(node: JsonNode, path: String): Option[String] = {
      if (node.isTextual) {
        Some(node.textValue())
      } else if (node.isObject && node.size() == 1 && node.has("type") && node.get("type").isTextual) {
        warnings += s"$path: Object-form enum values are deprecated; use a JSON string."
        Some(node.get("type").textValue())
      } else {
        errors += s"$path: Expected a JSON string."
        None
      }
    }

    private def stringMap(obj: ObjectNode, field: String, parent: String): Option[Map[String, String]] = {
      val node = obj.get(field)
      if (node == null) {
        return None
      }
      val path = s"$parent.$field"
      if (!node.isObject) {
        errors += s"$path: Expected a JSON object with string values."
        return None
      }

      val values = Map.newBuilder[String, String]
      node.properties().asScala.foreach { entry =>
        if (entry.getValue.isTextual) {
          values += entry.getKey -> entry.getValue.textValue()
        } else {
          errors += s"$path.${entry.getKey}: Expected a JSON string."
        }
      }
      Some(values.result())
    }

    private def stringList(obj: ObjectNode, field: String, parent: String): Option[List[String]] =
      stringListNode(Option(obj.get(field)), s"$parent.$field")

    private def stringListNode(node: Option[JsonNode], path: String): Option[List[String]] =
      node match {
        case None =>
          None
        case Some(value) if !value.isArray =>
          errors += s"$path: Expected an array of strings."
          None
        case Some(value) =>
          val values = ListBuffer.empty[String]
          value.elements().asScala.zipWithIndex.foreach { case (item, index) =>
            if (item.isTextual) {
              values += item.textValue()
            } else {
              errors += s"$path[$index]: Expected a JSON string."
            }
          }
          Some(values.toList)
      }

    private def text(obj: ObjectNode, field: String, parent: String): Option[String] =
      textNode(Option(obj.get(field)), s"$parent.$field")

    private def textNode(node: Option[JsonNode], path: String): Option[String] =
      node match {
        case None =>
          None
        case Some(value) if value.isTextual =>
          Some(value.textValue())
        case Some(_) =>
          errors += s"$path: Expected a JSON string."
          None
      }

    private def pathValue(obj: ObjectNode, field: String, parent: String): Option[Path] =
      text(obj, field, parent) match {
        case Some(value) => expandedPath(value, s"$parent.$field")
        case None        => None
      }

    private def boolean(obj: ObjectNode, field: String, parent: String): Option[Boolean] =
      booleanNode(Option(obj.get(field)), s"$parent.$field")

    private def booleanNode(node: Option[JsonNode], path: String): Option[Boolean] =
      node match {
        case None =>
          None
        case Some(value) if value.isBoolean =>
          Some(value.booleanValue())
        case Some(_) =>
          errors += s"$path: Expected a JSON boolean."
          None
      }

    private def integer(obj: ObjectNode, field: String, parent: String): Option[Int] =
      integerNode(Option(obj.get(field)), s"$parent.$field")

    private def integerNode(node: Option[JsonNode], path: String): Option[Int] =
      node match {
        case None =>
          None
        case Some(value) if value.isIntegralNumber && value.canConvertToInt =>
          Some(value.intValue())
        case Some(_) =>
          errors += s"$path: Expected a 32-bit JSON integer."
          None
      }

    private def negate(value: Option[Boolean]): Option[Boolean] =
      value match {
        case Some(boolean) => Some(!boolean)
        case None          => None
      }

    private def objectField(obj: ObjectNode, field: String, parent: String): Option[ObjectNode] = {
      val node = obj.get(field)
      if (node == null) {
        None
      } else if (node.isObject) {
        Some(node.asInstanceOf[ObjectNode])
      } else {
        errors += s"$parent.$field: Expected a JSON object."
        None
      }
    }

    /**
     * Parse the canonical and aliased names. Issue a deprecation warning on alias. This is required for
     * backward-compatibility with Quint.
     */
    private def aliased(
        obj: ObjectNode,
        canonical: String,
        aliases: Seq[String],
        parent: String): Option[JsonNode] = {
      val presentAliases = aliases.filter(obj.has)
      if (obj.has(canonical) && presentAliases.nonEmpty) {
        errors += s"$parent: Do not set both \"$canonical\" and its deprecated alias \"${presentAliases.head}\"."
        None
      } else if (obj.has(canonical)) {
        Some(obj.get(canonical))
      } else if (presentAliases.nonEmpty) {
        val alias = presentAliases.head
        warnings += s"$parent.$alias is deprecated; use $parent.$canonical."
        Some(obj.get(alias))
      } else {
        None
      }
    }

    private def rejectUnknown(obj: ObjectNode, path: String, allowed: Set[String]): Unit =
      obj.fieldNames().asScala.filterNot(allowed).foreach { field =>
        errors += s"$path.$field: Unknown configuration key."
      }

    private def recordSource(
        result: ConfigParseResult[InputSource.FileSource],
        path: String): Option[InputSource] = {
      if (result.isSuccess) {
        Some(result.requireValue(): InputSource)
      } else {
        result.errors.foreach(error => errors += s"$path: $error")
        None
      }
    }

    private def expandPath(value: String): Path = {
      if (value == "~") {
        Path.of(System.getProperty("user.home"))
      } else if (value.startsWith("~/") || value.startsWith("~\\")) {
        Path.of(System.getProperty("user.home")).resolve(value.substring(2))
      } else {
        Path.of(value)
      }
    }

    private def expandedPath(value: String, path: String): Option[Path] =
      try {
        Some(expandPath(value))
      } catch {
        case e: InvalidPathException =>
          errors += s"$path: Invalid path: ${e.getReason}"
          None
      }
  }

  private def writeTopLevelOptions(root: ObjectNode, config: ApalacheConfig): Unit = {
    put(root, "command", config.context.command)
    putPath(root, "config-file", config.context.configFile)
    putPath(root, "out-dir", config.common.outDir)
    putPath(root, "run-dir", config.common.runDir)
    putBoolean(root, "debug", config.common.debug)
    putBoolean(root, "smtprof", config.common.smtprof)
    putBoolean(root, "write-intermediate", config.common.writeIntermediate)
    putBoolean(root, "profiling", config.common.profiling)
    config.common.features.foreach { features =>
      val values = root.putArray("features")
      features.foreach(feature => values.add(feature.toString))
    }
    config.source.foreach(source => root.set[JsonNode]("source", sourceNode(source)))
    putPath(root, "output", config.output)
  }

  // Section writers omit absent fields and leave empty sections out of the document.
  private def writeChecker(root: ObjectNode, checker: CheckerPatch): Unit = {
    val obj = mapper.createObjectNode()
    checker.tuning.foreach { values =>
      val tuning = obj.putObject("tuning")
      values.foreach { case (key, value) => tuning.put(key, value) }
    }
    putNamed(obj, "algo", checker.algorithm, (value: Algorithm) => value.name)
    putPath(obj, "config", checker.tlcConfig)
    putBoolean(obj, "discard-disabled", checker.discardDisabled)
    put(obj, "cinit", checker.constantInitializer)
    put(obj, "init", checker.init)
    putList(obj, "inv", checker.invariants)
    put(obj, "next", checker.next)
    putInt(obj, "length", checker.length)
    putInt(obj, "max-error", checker.maxError)
    putInt(obj, "timeout-smt", checker.timeoutSmtSeconds)
    checker.checkDeadlocks.foreach(value => obj.put("no-deadlock", !value))
    putNamed(obj, "smt-solver", checker.smtSolver, (value: SMTSolver) => value.name)
    putNamed(obj, "smt-encoding", checker.smtEncoding, (value: SMTEncoding) => value.name)
    putList(obj, "temporal", checker.temporalProperties)
    put(obj, "view", checker.view)
    setIfNonEmpty(root, "checker", obj)
  }

  private def writeTypechecker(root: ObjectNode, typechecker: TypecheckerPatch): Unit = {
    val obj = mapper.createObjectNode()
    putBoolean(obj, "infer-poly", typechecker.inferPoly)
    setIfNonEmpty(root, "typechecker", obj)
  }

  private def writeTrace(root: ObjectNode, trace: TraceEvaluationPatch): Unit = {
    val obj = mapper.createObjectNode()
    trace.trace.foreach(source => obj.set[JsonNode]("trace", sourceNode(source)))
    putList(obj, "expressions", trace.expressions)
    setIfNonEmpty(root, "tracee", obj)
  }

  private def writeServer(root: ObjectNode, server: ServerPatch): Unit = {
    val obj = mapper.createObjectNode()
    putInt(obj, "port", server.port)
    putNamed(obj, "server-type", server.serverType, (value: ServerType) => value.name)
    setIfNonEmpty(root, "server", obj)
  }

  // Leaf writers preserve the sparse-configuration contract by emitting only present values.
  private def sourceNode(source: InputSource): JsonNode =
    source match {
      case InputSource.FileSource(path, format) =>
        val inferred = InputSource.FileSource(path)
        if (inferred.isSuccess && inferred.requireValue().format == format) {
          mapper.getNodeFactory.textNode(path.toString)
        } else {
          val obj = mapper.createObjectNode()
          obj.put("kind", "file")
          obj.put("path", path.toString)
          obj.put("format", format.name)
          obj
        }

      case value: InputSource.StringSource =>
        val obj = mapper.createObjectNode()
        obj.put("kind", "string")
        obj.put("content", value.content)
        val aux = obj.putArray("aux")
        value.aux.foreach(aux.add)
        obj.put("format", value.format.name)
        obj
    }

  private def put(obj: ObjectNode, field: String, value: Option[String]): Unit =
    value.foreach(obj.put(field, _))

  private def putPath(obj: ObjectNode, field: String, value: Option[Path]): Unit =
    value.foreach(path => obj.put(field, path.toString))

  private def putBoolean(obj: ObjectNode, field: String, value: Option[Boolean]): Unit =
    value.foreach(obj.put(field, _))

  private def putInt(obj: ObjectNode, field: String, value: Option[Int]): Unit =
    value.foreach(obj.put(field, _))

  private def putList[A](obj: ObjectNode, field: String, value: Option[List[A]]): Unit =
    value.foreach { items =>
      val array = obj.putArray(field)
      items.foreach(item => array.add(item.toString))
    }

  private def putNamed[A](
      obj: ObjectNode,
      field: String,
      value: Option[A],
      name: A => String): Unit =
    value.foreach(item => obj.put(field, name(item)))

  private def setIfNonEmpty(root: ObjectNode, field: String, value: ObjectNode): Unit =
    if (!value.isEmpty) root.set[JsonNode](field, value)
}
