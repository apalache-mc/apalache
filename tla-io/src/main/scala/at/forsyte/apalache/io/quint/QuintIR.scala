package at.forsyte.apalache.io.quint

// This package uses upickle's macros to generate serialization functions for
// the quint AST and associated output data.
//
// See https://com-lihaoyi.github.io/upickle/#Builtins for documentation on
// upickle semi-automatic JSON serialization docs.
//
//
//////////////////////////
// >> DEBUGGING TIPS << //
//////////////////////////
//
// When serialization fails, it will give an error of the form
//
//    expected <JSON value> got <diff JSON value> at index <N>
//
// E.g.,
//
//    expected sequence got dictionary at index 525
//
// The _index_ is the character count of the JSON data. To debug,
// first get quint's JSON representation of the spec with
//
//    quint typecheck --out spec.qnt.json spec.qnt
//
// Then look at the JSON data at the Nth character of spec.qnt.json.
// Comparing this against the IR datastructure defined below, in the
// context upickle serialization referenced above should make the
// problem clear.

// The `key` package allows customizing the JSON key for a class tag or attribute
// See https://com-lihaoyi.github.io/upickle/#CustomKeys
import upickle.implicits.key
import upickle.core.{Abort, Visitor}

import scala.util.Try

// We use a slightly customized deserializer
private[quint] object QuintDeserializer extends upickle.AttributeTagged {

  // By default, upickle uses the key `"$type"` to differentiate cases of a case
  // class, but quint uses the key `"kind"` to encode the variant tag. This
  // override forms a custom deserializer that is just like the default, except
  // the value of "kind" is used to differentiate
  override def tagName = "kind"

  // Override the built-in BigInt{Reader,Writer} to also support reading/writing
  // from/to JSON numbers.
  implicit override val BigIntWriter: QuintDeserializer.Writer[BigInt] = new Writer[BigInt] {
    override def write0[V](out: Visitor[_, V], v: BigInt): V = out.visitFloat64StringParts(v.toString(), -1, -1, 0)
  }
  implicit override val BigIntReader: QuintDeserializer.Reader[BigInt] = {
    new NumericReader[BigInt] {
      override def expectedMsg = "expected bigint"

      // Below, `index` is the character offset of the lexical unit to be parsed inside the JSON string
      override def visitString(s: CharSequence, index: Int) = visitFloat64String(s.toString, index)
      override def visitInt32(d: Int, index: Int) = BigInt(d)
      override def visitInt64(d: Long, index: Int) = BigInt(d)
      override def visitUInt64(d: Long, index: Int) = BigInt(d)
      override def visitFloat32(d: Float, index: Int) = BigDecimal(d).toBigIntExact match {
        case Some(bigInt) => bigInt
        case None         => throw Abort(expectedMsg + " got decimal (as float32)")
      }
      override def visitFloat64(d: Double, index: Int) = BigDecimal(d).toBigIntExact match {
        case Some(bigInt) => bigInt
        case None         => throw Abort(expectedMsg + " got decimal (as float64)")
      }
      override def visitFloat64StringParts(
          s: CharSequence,
          decIndex: Int,
          expIndex: Int,
          index: Int) = {
        if (decIndex != -1) {
          throw Abort(expectedMsg + " got decimal (as float64StringParts)")
        }
        if (expIndex != -1) {
          throw Abort(expectedMsg + " got exp notation (as float64StringParts)")
        }
        BigInt(s.toString)
      }
    }
  }
}

import QuintDeserializer.{macroRW, ReadWriter => RW}

// Internal error
private[quint] class QuintIRParseError(errMsg: String)
    extends Exception("Input was not a valid representation of the QuintIR: " + errMsg)

// User facing error
class QuintUnsupportedError(errMsg: String) extends Exception("Unsupported quint input: " + errMsg)

private[quint] case class QuintLookupTableEntry(
    kind: String,
    reference: BigInt)
private[quint] object QuintLookupTableEntry {
  implicit val rw: RW[QuintLookupTableEntry] = macroRW
}

/** The JSON output produced by quint parse */
private[quint] case class QuintOutput(
    stage: String,
    modules: Seq[QuintModule],
    // Maps source IDs to types, see the `WithId` trait
    types: Map[BigInt, QuintTypeScheme],
    // Maps name IDs to declaration IDs
    table: Map[BigInt, QuintLookupTableEntry])

object QuintOutput {
  implicit val rw: RW[QuintOutput] = macroRW

  def read(s: ujson.Readable): Try[QuintOutput] =
    Try(QuintDeserializer.read[QuintOutput](s)).recoverWith { case err: upickle.core.AbortException =>
      scala.util.Failure(new QuintIRParseError(s"${err.getMessage()}"))
    }
}

private[quint] case class QuintModule(
    id: BigInt,
    name: String,
    defs: Seq[QuintDef])
private[quint] object QuintModule {
  implicit val rw: RW[QuintModule] = macroRW
}

/** The representation of types in the type map */
private[quint] case class QuintTypeScheme(
    @key("type") typ: QuintType
    // TODO Will we need these for anything?
    // typeVariables: List[String],
    // rowVariables: List[String]
  )
private[quint] object QuintTypeScheme {
  implicit val rw: RW[QuintTypeScheme] = macroRW
}

/** Source IDs, used to associate expressions with their inferred types */
private[quint] trait WithID {
  val id: BigInt
}

/** The representation of quint expressions */
sealed private[quint] trait QuintEx extends WithID

private[quint] object QuintEx {

  implicit val rw: RW[QuintEx] =
    RW.merge(
        QuintName.rw,
        QuintBool.rw,
        QuintInt.rw,
        QuintStr.rw,
        QuintApp.rw,
        QuintLambda.rw,
        QuintLet.rw,
    )

  /** A name of: a variable, constant, parameter, user-defined operator */
  @key("name") case class QuintName(id: BigInt, name: String) extends QuintEx {}
  object QuintName {
    implicit val rw: RW[QuintName] = macroRW
  }

  /** The boolean literal value */
  @key("bool") case class QuintBool(id: BigInt, value: Boolean) extends QuintEx {}
  object QuintBool {
    implicit val rw: RW[QuintBool] = macroRW
  }

  @key("int") case class QuintInt(id: BigInt, value: BigInt) extends QuintEx {}
  object QuintInt {
    implicit val rw: RW[QuintInt] = macroRW
  }

  @key("str") case class QuintStr(id: BigInt, value: String) extends QuintEx {}
  object QuintStr {
    implicit val rw: RW[QuintStr] = macroRW
  }

  @key("app") case class QuintApp(
      id: BigInt,
      /** The name of the operator being applied */
      opcode: String,
      /** A list of arguments to the operator */
      args: Seq[QuintEx])
      extends QuintEx {}
  object QuintApp {
    implicit val rw: RW[QuintApp] = macroRW
  }

  case class QuintLambdaParameter(
      id: BigInt,
      name: String)
  object QuintLambdaParameter {
    implicit val rw: RW[QuintLambdaParameter] = macroRW
  }

  @key("lambda") case class QuintLambda(
      id: BigInt,
      /** Identifiers for the formal parameters */
      params: Seq[QuintLambdaParameter],
      /** The qualifier for the defined operator */
      // TODO should this eventually be a sumtype?
      qualifier: String,
      /** The definition body */
      expr: QuintEx)
      extends QuintEx {}
  object QuintLambda {
    implicit val rw: RW[QuintLambda] = macroRW
  }

  @key("let") case class QuintLet(
      id: BigInt,
      /** The operator being defined for use in the body */
      opdef: QuintDef.QuintOpDef,
      /** The body */
      expr: QuintEx)
      extends QuintEx {}
  object QuintLet {
    implicit val rw: RW[QuintLet] = macroRW
  }
}

/** quint Definitions (e.g., of types, operators, constants, etc.) */
sealed private[quint] trait QuintDef extends WithID

private[quint] object QuintDef {
  // The boilerplate here is a result of the infectious nature
  // of ser/de customization in upickle currently.
  // See https://github.com/com-lihaoyi/upickle/issues/394
  //
  // The customization is needed for QuintTypeDef.
  private val toJson: QuintDef => ujson.Value = {
    case d: QuintOpDef   => QuintDeserializer.writeJs(d)
    case d: QuintVar     => QuintDeserializer.writeJs(d)
    case d: QuintConst   => QuintDeserializer.writeJs(d)
    case d: QuintAssume  => QuintDeserializer.writeJs(d)
    case d: QuintTypeDef => QuintDeserializer.writeJs(d)
  }
  private val ofJson: ujson.Value => QuintDef = {
    case ujson.Obj(o) if o.get("kind").isDefined =>
      o.get("kind").map(_.str) match {
        case Some("def")     => QuintDeserializer.read[QuintOpDef](o)
        case Some("const")   => QuintDeserializer.read[QuintConst](o)
        case Some("var")     => QuintDeserializer.read[QuintVar](o)
        case Some("assume")  => QuintDeserializer.read[QuintAssume](o)
        case Some("typedef") => QuintDeserializer.read[QuintTypeDef](o)
        case Some(_)         => throw new QuintIRParseError(s"Definition has invalid `kind` field: ${o}")
        case None            => throw new QuintIRParseError(s"Definition missing `kind` field: ${o}")
      }
    case invalidJson =>
      throw new QuintIRParseError(s"Unexpected JSON representation of Quint type definition: ${invalidJson}")
  }

  implicit val rw: RW[QuintDef] = QuintDeserializer.readwriter[ujson.Value].bimap(toJson, ofJson)

  trait WithTypeAnnotation {
    val typeAnnotation: QuintType
  }

  /**
   * A user-defined operator
   *
   * Note that QuintOpDef does not have any formal parameters. If an operator definition has formal parameters, then
   * `expr` is a lambda expression over those parameters.
   *
   * NOTE: The QuintIR includes an optional type annotation in operator defs, but we have no use for it, as the final
   * type of any operator declaration is given in the type map. So we simply omit it.
   */
  @key("def") case class QuintOpDef(
      id: BigInt,
      /** definition name */
      name: String,
      /** qualifiers that identify definition kinds, like `def`, `val`, etc. */
      qualifier: String,
      /** expression to be associated with the definition */
      expr: QuintEx)
      extends QuintDef {}
  object QuintOpDef {
    implicit val rw: RW[QuintOpDef] = macroRW
  }

  @key("const") case class QuintConst(
      id: BigInt,
      /** name of the constant */
      name: String,
      typeAnnotation: QuintType)
      extends QuintDef with WithTypeAnnotation {}
  object QuintConst {
    implicit val rw: RW[QuintConst] = macroRW
  }

  @key("var") case class QuintVar(
      id: BigInt,
      /** name of the variable */
      name: String,
      typeAnnotation: QuintType)
      extends QuintDef with WithTypeAnnotation {}
  object QuintVar {
    implicit val rw: RW[QuintVar] = macroRW
  }

  @key("assume") case class QuintAssume(
      id: BigInt,
      /** name of the assumption, may be '_' */
      name: String,
      /** an expression to associate with the name */
      assumption: QuintEx)
      extends QuintDef {}
  object QuintAssume {
    implicit val rw: RW[QuintAssume] = macroRW
  }

  /**
   * QuintTypeDefs represent both type aliases and abstract types
   *
   *   - Abstract types do not have an associated `type`
   *   - Type aliases always have an associated `type`
   */
  @key("typedef") case class QuintTypeDef(
      id: BigInt,
      /** name of a type alias */
      name: String,
      /**
       * type to associate with the alias (none for uninterpreted type)
       *
       * Type aliases have `Some(type)` while abstract types have `None`
       */
      typ: Option[QuintType])
      extends QuintDef {}
  object QuintTypeDef {
    // We need custom ser/de here to cope with the optionality of the `type` field
    // see https://github.com/com-lihaoyi/upickle/issues/75
    private val toJson: QuintTypeDef => ujson.Value = {
      case QuintTypeDef(id, name, None) =>
        ujson.Obj("id" -> QuintDeserializer.writeJs(id), "name" -> QuintDeserializer.writeJs(name))
      case QuintTypeDef(id, name, Some(t)) =>
        ujson.Obj("id" -> QuintDeserializer.writeJs(id), "name" -> QuintDeserializer.writeJs(name),
            "type" -> QuintDeserializer.writeJs(t))
    }

    private val ofJson: ujson.Value => QuintTypeDef = {
      case ujson.Obj(entries) if entries.get("id").isDefined && entries.get("name").isDefined =>
        val id = QuintDeserializer.read[BigInt](entries.get("id").get)
        val name = QuintDeserializer.read[String](entries.get("name").get)
        val tt = entries.get("type").map(t => QuintDeserializer.read[QuintType](t))
        QuintTypeDef(id, name, tt)
      case invalidJson =>
        throw new QuintIRParseError(s"Unexpected JSON representation of Quint type definition: ${invalidJson}")
    }

    implicit val rw: RW[QuintTypeDef] = QuintDeserializer.readwriter[ujson.Value].bimap(toJson, ofJson)
  }
}

/**
 * quint Types
 *
 * Note that quint types have an optional associated source ID. We ignore that in our representation currently, as we
 * have no use for source IDs on types.
 */
sealed private[quint] trait QuintType

private[quint] object QuintType {

  implicit val rw: RW[QuintType] = RW.merge(
      QuintBoolT.rw,
      QuintIntT.rw,
      QuintStrT.rw,
      QuintConstT.rw,
      QuintVarT.rw,
      QuintSetT.rw,
      QuintSeqT.rw,
      QuintFunT.rw,
      QuintOperT.rw,
      QuintTupleT.rw,
      QuintRecordT.rw,
      QuintUnionT.rw,
  )

  // NOTE: Contrary to quint values, for quint types, source IDs are optional.
  // This is because many types are inferred, and not derived from the soruce.
  //
  // We therefor default id to -1 in the following, because upickle handles
  // optional values stupidly and if we specify `id` as `Option[Int]` it will
  // require the value of the ID field to be a (possibly empty) singleton array.

  @key("bool") case class QuintBoolT() extends QuintType {}
  object QuintBoolT {
    implicit val rw: RW[QuintBoolT] = macroRW
  }

  @key("int") case class QuintIntT() extends QuintType
  object QuintIntT {
    implicit val rw: RW[QuintIntT] = macroRW
  }

  @key("str") case class QuintStrT() extends QuintType
  object QuintStrT {
    implicit val rw: RW[QuintStrT] = macroRW
  }

  @key("const") case class QuintConstT(name: String) extends QuintType
  object QuintConstT {
    implicit val rw: RW[QuintConstT] = macroRW
  }

  @key("var") case class QuintVarT(name: String) extends QuintType
  object QuintVarT {
    implicit val rw: RW[QuintVarT] = macroRW
  }

  @key("set") case class QuintSetT(elem: QuintType) extends QuintType
  object QuintSetT {
    implicit val rw: RW[QuintSetT] = macroRW
  }

  @key("list") case class QuintSeqT(elem: QuintType) extends QuintType
  object QuintSeqT {
    implicit val rw: RW[QuintSeqT] = macroRW
  }

  @key("fun") case class QuintFunT(arg: QuintType, res: QuintType) extends QuintType
  object QuintFunT {
    implicit val rw: RW[QuintFunT] = macroRW
  }

  @key("oper") case class QuintOperT(args: Seq[QuintType], res: QuintType) extends QuintType
  object QuintOperT {
    implicit val rw: RW[QuintOperT] = macroRW
  }

  case class RecordField(fieldName: String, fieldType: QuintType)
  object RecordField {
    implicit val rw: RW[RecordField] = macroRW
  }

  sealed trait Row

  object Row {
    implicit val rw: RW[Row] = RW.merge(Cell.rw, Var.rw, Nil.rw)

    @key("row") case class Cell(fields: Seq[RecordField], other: Row) extends Row
    object Cell {
      implicit val rw: RW[Cell] = macroRW
    }

    @key("var") case class Var(name: String) extends Row
    object Var {
      implicit val rw: RW[Var] = macroRW
    }

    @key("empty") case class Nil() extends Row
    object Nil {
      implicit val rw: RW[Nil] = macroRW
    }
  }

  @key("tup") case class QuintTupleT(fields: Row) extends QuintType
  object QuintTupleT {
    implicit val rw: RW[QuintTupleT] = macroRW

    // Helper for manually constructing tuple types
    def ofTypes(types: QuintType*): QuintTupleT = {
      val fields = types.zipWithIndex.map { case (t, i) => RecordField(i.toString, t) }
      QuintTupleT(Row.Cell(fields, Row.Nil()))
    }
  }

  @key("rec") case class QuintRecordT(fields: Row) extends QuintType {

    // `r.rowVar` is `Some(s)` if it is an open row and `s` is the name of the row variable.
    // Otherwise it is `None`.
    def rowVar: Option[String] = getVar(fields)

    private val getVar: Row => Option[String] = {
      case Row.Var(v)           => Some(v)
      case Row.Nil()            => None
      case Row.Cell(_, moreRow) => getVar(moreRow)
    }
  }

  object QuintRecordT {
    implicit val rw: RW[QuintRecordT] = macroRW

    // Helper for manually constructing record type
    def ofFieldTypes(fieldTypes: (String, QuintType)*): QuintRecordT = {
      val fields = fieldTypes.map { case (f, t) => RecordField(f, t) }
      QuintRecordT(Row.Cell(fields, Row.Nil()))
    }

    // Helper for manually constructing record type with free row variable
    def ofFieldTypes(rowVar: String, fieldTypes: (String, QuintType)*): QuintRecordT = {
      val fields = fieldTypes.map { case (f, t) => RecordField(f, t) }
      QuintRecordT(Row.Cell(fields, Row.Var(rowVar)))
    }
  }

  case class UnionRecord(tagValue: String, fields: Row)
  object UnionRecord {
    implicit val rw: RW[UnionRecord] = macroRW
  }

  @key("union") case class QuintUnionT(tag: String, records: Seq[UnionRecord]) extends QuintType
  object QuintUnionT {
    implicit val rw: RW[QuintUnionT] = macroRW
  }
}
