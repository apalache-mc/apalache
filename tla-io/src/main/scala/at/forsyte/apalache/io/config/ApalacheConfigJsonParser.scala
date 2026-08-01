package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.tla.lir.Feature
import com.fasterxml.jackson.core.{JsonFactory, JsonParser}
import com.fasterxml.jackson.databind.node.ObjectNode
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}

import java.nio.file.{InvalidPathException, Path}
import scala.jdk.CollectionConverters._

/**
 * Strict JSON parser and writer for sparse `ApalacheConfig` values.
 *
 * [[parse]] parses and checks one JSON document; [[write]] emits canonical JSON without applying source precedence,
 * runtime defaults, or mode-specific validation. `JsonDecoder` maps JSON fields and sections to patch classes with
 * `Either`, accumulating independent diagnostics without mutable decoder state. The `decode*` and `write*` methods
 * handle top-level structures; the remaining helpers handle leaf values.
 *
 * The package model and maintenance rules are documented in the
 * [[https://github.com/apalache-mc/apalache/blob/main/tla-io/src/main/scala/at/forsyte/apalache/io/config/README.md package README]].
 */
object ApalacheConfigJsonParser {

  import Constants._

  // either a list of errors, or a result
  private type DecodeResult[A] = Either[List[String], A]

  private val factory = new JsonFactory()
  factory.enable(JsonParser.Feature.STRICT_DUPLICATE_DETECTION)
  private val mapper = new ObjectMapper(factory)

  /** Parse one strict JSON document into a sparse configuration, using `sourceName` to identify diagnostics. */
  def parse(
      sourceText: String,
      sourceName: String = "<configuration>"): ConfigParseResult[ApalacheConfig] =
    decodeRoot(sourceText, sourceName).flatMap(JsonDecoder.config) match {
      case Right(config)     => ConfigParseResult.success(config)
      case Left(diagnostics) => ConfigParseResult.failure(diagnostics)
    }

  /** Parse and validate the root JSON node before decoding configuration fields. */
  private def decodeRoot(sourceText: String, sourceName: String): DecodeResult[ObjectNode] =
    try {
      val parser = mapper.createParser(sourceText)
      try {
        val root: DecodeResult[JsonNode] = Option(mapper.readTree[JsonNode](parser)) match {
          case Some(value) => Right(value)
          case None        => decodeFailure(s"$sourceName: Expected a JSON object, but the document is empty.")
        }
        val endOfDocument: DecodeResult[Unit] =
          if (parser.nextToken() == null) Right(())
          else decodeFailure(s"$sourceName: Trailing content after the JSON document is not allowed.")

        combine(root, endOfDocument)((value, _) => value).flatMap { value =>
          if (value.isObject) Right(value.asInstanceOf[ObjectNode])
          else decodeFailure(s"$sourceName: Expected the configuration root to be a JSON object.")
        }
      } finally {
        parser.close()
      }
    } catch {
      case e: Exception => decodeFailure(s"$sourceName: Invalid strict JSON: ${e.getMessage}")
    }

  private def decodeFailure[A](diagnostic: String): DecodeResult[A] = Left(List(diagnostic))

  /** Combine independent decode results and retain diagnostics from both sides. */
  private def combine[A, B, C](
      first: DecodeResult[A],
      second: DecodeResult[B],
    )(f: (A, B) => C): DecodeResult[C] =
    (first, second) match {
      case (Right(a), Right(b))   => Right(f(a, b))
      case (Left(a), Left(b))     => Left(a ++ b)
      case (Left(diagnostics), _) => Left(diagnostics)
      case (_, Left(diagnostics)) => Left(diagnostics)
    }

  /** Sequence homogeneous decode results while retaining every independent diagnostic. */
  private def collect[A](results: Iterable[DecodeResult[A]]): DecodeResult[List[A]] =
    results.toList.foldRight[DecodeResult[List[A]]](Right(Nil)) { (result, collected) =>
      combine(result, collected)(_ :: _)
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

  /** Stateless translation from JSON nodes to sparse configuration patches. */
  private object JsonDecoder {

    /** Decode all recognized top-level keys and sections. */
    def config(root: ObjectNode): DecodeResult[ApalacheConfig] =
      build(
          ApalacheConfig(),
          validation(rejectUnknown(
                  root,
                  "$",
                  Set(
                      COMMAND,
                      CONFIG_FILE,
                      OUT_DIR,
                      RUN_DIR,
                      DEBUG,
                      SMTPROF,
                      WRITE_INTERMEDIATE,
                      PROFILING,
                      FEATURES,
                      SOURCE,
                      OUTPUT,
                      CHECKER,
                      TYPECHECKER,
                      TRACEE,
                      SERVER,
                  ),
              )),
          update(decodeContext(root))((config, context) => config.copy(context = context)),
          update(decodeCommon(root))((config, common) => config.copy(common = common)),
          update(source(root, SOURCE, "$"))((config, value) => config.copy(source = value)),
          update(pathValue(root, OUTPUT, "$"))((config, value) => config.copy(output = value)),
          update(decodeChecker(root))((config, checker) => config.copy(checker = checker)),
          update(decodeTypechecker(root))((config, typechecker) => config.copy(typechecker = typechecker)),
          update(decodeTrace(root))((config, trace) => config.copy(traceEvaluation = trace)),
          update(decodeServer(root))((config, server) => config.copy(server = server)),
      )

    private def decodeContext(root: ObjectNode): DecodeResult[RunContextPatch] =
      build(
          RunContextPatch(),
          update(text(root, COMMAND, "$"))((context, value) => context.copy(command = value)),
          update(pathValue(root, CONFIG_FILE, "$"))((context, value) => context.copy(configFile = value)),
      )

    private def decodeCommon(root: ObjectNode): DecodeResult[CommonPatch] =
      build(
          CommonPatch(),
          update(pathValue(root, OUT_DIR, "$"))((common, value) => common.copy(outDir = value)),
          update(pathValue(root, RUN_DIR, "$"))((common, value) => common.copy(runDir = value)),
          update(boolean(root, DEBUG, "$"))((common, value) => common.copy(debug = value)),
          update(boolean(root, SMTPROF, "$"))((common, value) => common.copy(smtprof = value)),
          update(boolean(root, WRITE_INTERMEDIATE, "$"))((common, value) => common.copy(writeIntermediate = value)),
          update(boolean(root, PROFILING, "$"))((common, value) => common.copy(profiling = value)),
          update(featureList(root, FEATURES, "$"))((common, value) => common.copy(features = value)),
      )

    private def decodeChecker(root: ObjectNode): DecodeResult[CheckerPatch] =
      objectField(root, CHECKER, "$").flatMap {
        case None =>
          Right(CheckerPatch())

        case Some(obj) =>
          val path = s"$$.$CHECKER"
          build(
              CheckerPatch(),
              validation(rejectUnknown(
                      obj,
                      path,
                      Set(
                          TUNING,
                          ALGO,
                        SEARCH_KIND,
                        SEED,
                        MAX_RUN,
                        OUTPUT_TRACES,
                          CONFIG,
                          DISCARD_DISABLED,
                          CINIT,
                          INIT,
                          INV,
                          NEXT,
                          LENGTH,
                          MAX_ERROR,
                          TIMEOUT_SMT,
                          NO_DEADLOCK,
                          SMT_SOLVER,
                          SMT_ENCODING,
                          TEMPORAL,
                          VIEW,
                      ),
                  )),
              update(stringMap(obj, TUNING, path))((checker: CheckerPatch, value) => checker.copy(tuning = value)),
              update(enumValue(obj, ALGO, path, Algorithm.fromString))((checker: CheckerPatch, value) =>
                checker.copy(algorithm = value)),
            update(enumValue(obj, SEARCH_KIND, path, SearchKind.fromString))((checker: CheckerPatch, value) =>
              checker.copy(searchKind = value)),
            update(integer(obj, SEED, path))((checker: CheckerPatch, value) => checker.copy(seed = value)),
            update(integer(obj, MAX_RUN, path))((checker: CheckerPatch, value) => checker.copy(maxRun = value)),
            update(boolean(obj, OUTPUT_TRACES, path))((checker: CheckerPatch, value) =>
              checker.copy(outputTraces = value)),
              update(pathValue(obj, CONFIG, path))((checker: CheckerPatch, value) => checker.copy(tlcConfig = value)),
              update(boolean(obj, DISCARD_DISABLED, path))((checker: CheckerPatch, value) =>
                checker.copy(discardDisabled = value)),
              update(text(obj, CINIT, path))((checker: CheckerPatch, value) =>
                checker.copy(constantInitializer = value)),
              update(text(obj, INIT, path))((checker: CheckerPatch, value) => checker.copy(init = value)),
              update(stringList(obj, INV, path))((checker: CheckerPatch, value) => checker.copy(invariants = value)),
              update(text(obj, NEXT, path))((checker: CheckerPatch, value) => checker.copy(next = value)),
              update(integer(obj, LENGTH, path))((checker: CheckerPatch, value) => checker.copy(length = value)),
              update(integer(obj, MAX_ERROR, path))((checker: CheckerPatch, value) => checker.copy(maxError = value)),
              update(integer(obj, TIMEOUT_SMT, path))((checker: CheckerPatch, value) =>
                checker.copy(timeoutSmtSeconds = value)),
              update(negate(boolean(obj, NO_DEADLOCK, path)))((checker: CheckerPatch, value) =>
                checker.copy(checkDeadlocks = value)),
              update(enumValue(obj, SMT_SOLVER, path, SMTSolver.fromString))((checker: CheckerPatch, value) =>
                checker.copy(smtSolver = value)),
              update(enumValue(obj, SMT_ENCODING, path, SMTEncoding.fromString))((checker: CheckerPatch, value) =>
                checker.copy(smtEncoding = value)),
              update(stringList(obj, TEMPORAL, path))((checker: CheckerPatch, value) =>
                checker.copy(temporalProperties = value)),
              update(text(obj, VIEW, path))((checker: CheckerPatch, value) => checker.copy(view = value)),
          )
      }

    private def decodeTypechecker(root: ObjectNode): DecodeResult[TypecheckerPatch] =
      objectField(root, TYPECHECKER, "$").flatMap {
        case None =>
          Right(TypecheckerPatch())
        case Some(obj) =>
          val path = s"$$.$TYPECHECKER"
          build(
              TypecheckerPatch(),
              validation(rejectUnknown(obj, path, Set(INFER_POLY))),
              update(boolean(obj, INFER_POLY, path))((typechecker: TypecheckerPatch, value) =>
                typechecker.copy(inferPoly = value)),
          )
      }

    private def decodeTrace(root: ObjectNode): DecodeResult[TraceEvaluationPatch] =
      objectField(root, TRACEE, "$").flatMap {
        case None =>
          Right(TraceEvaluationPatch())
        case Some(obj) =>
          val path = s"$$.$TRACEE"
          build(
              TraceEvaluationPatch(),
              validation(rejectUnknown(obj, path, Set(TRACE, EXPRESSIONS))),
              update(source(obj, TRACE, path))((trace: TraceEvaluationPatch, value) => trace.copy(trace = value)),
              update(stringList(obj, EXPRESSIONS, path))((trace: TraceEvaluationPatch, value) =>
                trace.copy(expressions = value)),
          )
      }

    private def decodeServer(root: ObjectNode): DecodeResult[ServerPatch] =
      objectField(root, SERVER, "$").flatMap {
        case None =>
          Right(ServerPatch())
        case Some(obj) =>
          val path = s"$$.$SERVER"
          build(
              ServerPatch(),
              validation(rejectUnknown(obj, path, Set(PORT, SERVER_TYPE))),
              update(integer(obj, PORT, path))((server: ServerPatch, value) => server.copy(port = value)),
              update(enumValue(obj, SERVER_TYPE, path, ServerType.fromString))((server: ServerPatch, value) =>
                server.copy(serverType = value)),
          )
      }

    // Optional fields are represented inside Right; malformed fields are represented by Left.
    private def source(obj: ObjectNode, field: String, parent: String): DecodeResult[Option[InputSource]] =
      Option(obj.get(field)) match {
        case None =>
          Right(None)

        case Some(node) =>
          val path = s"$parent.$field"
          if (node.isTextual) {
            expandedPath(node.textValue(), path)
              .flatMap(value => recordSource(InputSource.FileSource(value), path))
              .map(value => Some(value))
          } else if (node.isObject) {
            val sourceObj = node.asInstanceOf[ObjectNode]
            val decoded = sourceKind(sourceObj, path).flatMap {
              case FILE                    => decodeFileSource(sourceObj, path)
              case STRING                  => decodeStringSource(sourceObj, path)
              case other if other.nonEmpty =>
                decodeFailure(s"$path.$KIND: Expected \"$FILE\" or \"$STRING\", but got \"$other\".")
              case _ =>
                Right(None)
            }
            combine(
                rejectUnknown(sourceObj, path, Set(KIND, PATH, CONTENT, AUX, FORMAT)),
                decoded,
            )((_, value) => value)
          } else {
            decodeFailure(s"$path: Expected a path string or source object.")
          }
      }

    private def sourceKind(sourceObj: ObjectNode, path: String): DecodeResult[String] =
      if (sourceObj.has(KIND)) {
        text(sourceObj, KIND, path).map(_.map(_.toLowerCase).getOrElse(""))
      } else if (sourceObj.has(CONTENT)) {
        Right(STRING)
      } else if (sourceObj.has(PATH)) {
        Right(FILE)
      } else {
        decodeFailure(s"$path: Source object requires kind, path, or content.")
      }

    private def decodeFileSource(sourceObj: ObjectNode, path: String): DecodeResult[Option[InputSource]] =
      text(sourceObj, PATH, path).flatMap {
        case None =>
          Right(None)
        case Some(value) =>
          expandedPath(value, s"$path.$PATH").flatMap { sourcePath =>
            formatValue(sourceObj.get(FORMAT), s"$path.$FORMAT").flatMap {
              case Some(format) => Right(Some(InputSource.FileSource(sourcePath, format): InputSource))
              case None         =>
                recordSource(InputSource.FileSource(sourcePath), path).map(value => Some(value))
            }
          }
      }

    private def decodeStringSource(sourceObj: ObjectNode, path: String): DecodeResult[Option[InputSource]] = {
      val contentAndAux = combine(
          text(sourceObj, CONTENT, path),
          stringList(sourceObj, AUX, path),
      )((_, _))
      combine(contentAndAux, formatValue(sourceObj.get(FORMAT), s"$path.$FORMAT")) {
        case ((Some(content), aux), format) =>
          Some(InputSource.StringSource(
                  content,
                  aux.getOrElse(Nil),
                  format.getOrElse(InputSource.Format.Tla),
              ): InputSource)
        case _ =>
          None
      }
    }

    private def formatValue(node: JsonNode, path: String): DecodeResult[Option[InputSource.Format]] =
      Option(node) match {
        case None        => Right(None)
        case Some(value) =>
          scalarEnumText(value, path)
            .flatMap(convertValue(_, path, InputSource.Format.fromString))
            .map(value => Some(value))
      }

    private def featureList(
        obj: ObjectNode,
        field: String,
        parent: String): DecodeResult[Option[List[Feature]]] =
      stringList(obj, field, parent).flatMap {
        case None =>
          Right(None)
        case Some(strings) =>
          collect(strings.map { value =>
            Feature.fromString(value) match {
              case Some(feature) => Right(feature)
              case None          => decodeFailure(s"$parent.$field: Unexpected feature: $value")
            }
          }).map(values => Some(values))
      }

    private def enumValue[A](
        obj: ObjectNode,
        field: String,
        parent: String,
        fromString: String => A): DecodeResult[Option[A]] =
      Option(obj.get(field)) match {
        case None =>
          Right(None)
        case Some(node) =>
          val path = s"$parent.$field"
          scalarEnumText(node, path).flatMap(convertValue(_, path, fromString)).map(value => Some(value))
      }

    /** Convert an enum-like value into a path-qualified decode result. */
    private def convertValue[A](value: String, path: String, fromString: String => A): DecodeResult[A] =
      try {
        Right(fromString(value))
      } catch {
        case e: IllegalArgumentException => decodeFailure(s"$path: ${e.getMessage}")
      }

    private def scalarEnumText(node: JsonNode, path: String): DecodeResult[String] =
      if (node.isTextual) Right(node.textValue())
      else decodeFailure(s"$path: Expected a JSON string.")

    private def stringMap(
        obj: ObjectNode,
        field: String,
        parent: String): DecodeResult[Option[Map[String, String]]] =
      Option(obj.get(field)) match {
        case None =>
          Right(None)
        case Some(node) =>
          val path = s"$parent.$field"
          if (!node.isObject) {
            decodeFailure(s"$path: Expected a JSON object with string values.")
          } else {
            collect(node.properties().asScala.map { entry =>
              if (entry.getValue.isTextual) {
                Right(entry.getKey -> entry.getValue.textValue())
              } else {
                decodeFailure(s"$path.${entry.getKey}: Expected a JSON string.")
              }
            }).map(values => Some(values.toMap))
          }
      }

    private def stringList(
        obj: ObjectNode,
        field: String,
        parent: String): DecodeResult[Option[List[String]]] =
      stringListNode(Option(obj.get(field)), s"$parent.$field")

    private def stringListNode(node: Option[JsonNode], path: String): DecodeResult[Option[List[String]]] =
      node match {
        case None =>
          Right(None)
        case Some(value) if !value.isArray =>
          decodeFailure(s"$path: Expected an array of strings.")
        case Some(value) =>
          collect(value
                .elements()
                .asScala
                .zipWithIndex
                .map { case (item, index) =>
                  if (item.isTextual) Right(item.textValue())
                  else decodeFailure(s"$path[$index]: Expected a JSON string.")
                }
                .toList).map(values => Some(values))
      }

    private def text(obj: ObjectNode, field: String, parent: String): DecodeResult[Option[String]] =
      textNode(Option(obj.get(field)), s"$parent.$field")

    private def textNode(node: Option[JsonNode], path: String): DecodeResult[Option[String]] =
      node match {
        case None                           => Right(None)
        case Some(value) if value.isTextual => Right(Some(value.textValue()))
        case Some(_)                        => decodeFailure(s"$path: Expected a JSON string.")
      }

    private def pathValue(obj: ObjectNode, field: String, parent: String): DecodeResult[Option[Path]] =
      text(obj, field, parent).flatMap {
        case Some(value) => expandedPath(value, s"$parent.$field").map(path => Some(path))
        case None        => Right(None)
      }

    private def boolean(obj: ObjectNode, field: String, parent: String): DecodeResult[Option[Boolean]] =
      booleanNode(Option(obj.get(field)), s"$parent.$field")

    private def booleanNode(node: Option[JsonNode], path: String): DecodeResult[Option[Boolean]] =
      node match {
        case None                           => Right(None)
        case Some(value) if value.isBoolean => Right(Some(value.booleanValue()))
        case Some(_)                        => decodeFailure(s"$path: Expected a JSON boolean.")
      }

    private def integer(obj: ObjectNode, field: String, parent: String): DecodeResult[Option[Int]] =
      integerNode(Option(obj.get(field)), s"$parent.$field")

    private def integerNode(node: Option[JsonNode], path: String): DecodeResult[Option[Int]] =
      node match {
        case None =>
          Right(None)
        case Some(value) if value.isIntegralNumber && value.canConvertToInt =>
          Right(Some(value.intValue()))
        case Some(_) =>
          decodeFailure(s"$path: Expected a 32-bit JSON integer.")
      }

    private def negate(value: DecodeResult[Option[Boolean]]): DecodeResult[Option[Boolean]] =
      value.map(_.map(boolean => !boolean))

    private def objectField(
        obj: ObjectNode,
        field: String,
        parent: String): DecodeResult[Option[ObjectNode]] =
      Option(obj.get(field)) match {
        case None                        => Right(None)
        case Some(node) if node.isObject => Right(Some(node.asInstanceOf[ObjectNode]))
        case Some(_)                     => decodeFailure(s"$parent.$field: Expected a JSON object.")
      }

    private def rejectUnknown(obj: ObjectNode, path: String, allowed: Set[String]): DecodeResult[Unit] = {
      val diagnostics = obj
        .fieldNames()
        .asScala
        .filterNot(allowed)
        .map(field => s"$path.$field: Unknown configuration key.")
        .toList
      if (diagnostics.isEmpty) Right(()) else Left(diagnostics)
    }

    private def recordSource(
        result: ConfigParseResult[InputSource.FileSource],
        path: String): DecodeResult[InputSource] =
      if (result.isSuccess) {
        Right(result.requireValue(): InputSource)
      } else {
        Left(result.errors.map(error => s"$path: $error"))
      }

    private def expandPath(value: String): Path = {
      if (value == "~") {
        Path.of(System.getProperty(USER_HOME_PROPERTY))
      } else if (value.startsWith("~/") || value.startsWith("~\\")) {
        Path.of(System.getProperty(USER_HOME_PROPERTY)).resolve(value.substring(2))
      } else {
        Path.of(value)
      }
    }

    private def expandedPath(value: String, path: String): DecodeResult[Path] =
      try {
        Right(expandPath(value))
      } catch {
        case e: InvalidPathException => decodeFailure(s"$path: Invalid path: ${e.getReason}")
      }

    /** Apply independently decoded updates while retaining diagnostics from every update. */
    private def build[A](initial: A, updates: DecodeResult[A => A]*): DecodeResult[A] =
      updates.foldLeft[DecodeResult[A]](Right(initial)) { (current, decodedUpdate) =>
        combine(current, decodedUpdate)((value, applyUpdate) => applyUpdate(value))
      }

    private def update[A, B](decoded: DecodeResult[B])(f: (A, B) => A): DecodeResult[A => A] =
      decoded.map(value => current => f(current, value))

    private def validation[A](decoded: DecodeResult[Unit]): DecodeResult[A => A] =
      decoded.map(_ => identity[A])
  }

  private def writeTopLevelOptions(root: ObjectNode, config: ApalacheConfig): Unit = {
    put(root, COMMAND, config.context.command)
    putPath(root, CONFIG_FILE, config.context.configFile)
    putPath(root, OUT_DIR, config.common.outDir)
    putPath(root, RUN_DIR, config.common.runDir)
    putBoolean(root, DEBUG, config.common.debug)
    putBoolean(root, SMTPROF, config.common.smtprof)
    putBoolean(root, WRITE_INTERMEDIATE, config.common.writeIntermediate)
    putBoolean(root, PROFILING, config.common.profiling)
    config.common.features.foreach { features =>
      val values = root.putArray(FEATURES)
      features.foreach(feature => values.add(feature.toString))
    }
    config.source.foreach(source => root.set[JsonNode](SOURCE, sourceNode(source)))
    putPath(root, OUTPUT, config.output)
  }

  // Section writers omit absent fields and leave empty sections out of the document.
  private def writeChecker(root: ObjectNode, checker: CheckerPatch): Unit = {
    val obj = mapper.createObjectNode()
    checker.tuning.foreach { values =>
      val tuning = obj.putObject(TUNING)
      values.foreach { case (key, value) => tuning.put(key, value) }
    }
    putNamed(obj, ALGO, checker.algorithm, (value: Algorithm) => value.name)
    putNamed(obj, SEARCH_KIND, checker.searchKind, (value: SearchKind) => value.name)
    putInt(obj, SEED, checker.seed)
    putInt(obj, MAX_RUN, checker.maxRun)
    putBoolean(obj, OUTPUT_TRACES, checker.outputTraces)
    putPath(obj, CONFIG, checker.tlcConfig)
    putBoolean(obj, DISCARD_DISABLED, checker.discardDisabled)
    put(obj, CINIT, checker.constantInitializer)
    put(obj, INIT, checker.init)
    putList(obj, INV, checker.invariants)
    put(obj, NEXT, checker.next)
    putInt(obj, LENGTH, checker.length)
    putInt(obj, MAX_ERROR, checker.maxError)
    putInt(obj, TIMEOUT_SMT, checker.timeoutSmtSeconds)
    checker.checkDeadlocks.foreach(value => obj.put(NO_DEADLOCK, !value))
    putNamed(obj, SMT_SOLVER, checker.smtSolver, (value: SMTSolver) => value.name)
    putNamed(obj, SMT_ENCODING, checker.smtEncoding, (value: SMTEncoding) => value.name)
    putList(obj, TEMPORAL, checker.temporalProperties)
    put(obj, VIEW, checker.view)
    setIfNonEmpty(root, CHECKER, obj)
  }

  private def writeTypechecker(root: ObjectNode, typechecker: TypecheckerPatch): Unit = {
    val obj = mapper.createObjectNode()
    putBoolean(obj, INFER_POLY, typechecker.inferPoly)
    setIfNonEmpty(root, TYPECHECKER, obj)
  }

  private def writeTrace(root: ObjectNode, trace: TraceEvaluationPatch): Unit = {
    val obj = mapper.createObjectNode()
    trace.trace.foreach(source => obj.set[JsonNode](TRACE, sourceNode(source)))
    putList(obj, EXPRESSIONS, trace.expressions)
    setIfNonEmpty(root, TRACEE, obj)
  }

  private def writeServer(root: ObjectNode, server: ServerPatch): Unit = {
    val obj = mapper.createObjectNode()
    putInt(obj, PORT, server.port)
    putNamed(obj, SERVER_TYPE, server.serverType, (value: ServerType) => value.name)
    setIfNonEmpty(root, SERVER, obj)
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
          obj.put(KIND, FILE)
          obj.put(PATH, path.toString)
          obj.put(FORMAT, format.name)
          obj
        }

      case value: InputSource.StringSource =>
        val obj = mapper.createObjectNode()
        obj.put(KIND, STRING)
        obj.put(CONTENT, value.content)
        val aux = obj.putArray(AUX)
        value.aux.foreach(aux.add)
        obj.put(FORMAT, value.format.name)
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
