package at.forsyte.apalache.io.quint

// This package uses upickle's macros to generate serialization functions for
// the quint AST and associated output data.
//
// See https://com-lihaoyi.github.io/upickle/#Builtins for documentation on
// upickle semi-automatic JSON serialization docs.

// The `key` package allows customizing the JSON key for a class tag or attribute
// See https://com-lihaoyi.github.io/upickle/#CustomKeys
import upickle.implicits.key
import scala.util.Try

// We use a slightly customized deserializer
private[quint] object QuintDeserializer extends upickle.AttributeTagged {

  // By default, upickle uses the key `"$type"` to differentiate cases of a case
  // class, but quint uses the key `"kind"` to encode the variant tag. This
  // override forms a custom deserializer that is just like the default, except
  // the value of "kind" is used to differentiate
  override def tagName = "kind"

}

import QuintDeserializer.{macroRW, ReadWriter => RW}

// Internal error
private[quint] class QuintIRParseError(errMsg: String)
    extends Exception("Input was not a valid representation of the QuintIR: " + errMsg)

// User facing error
class QuintUnsupportedError(errMsg: String) extends Exception("Unsupported quint input: " + errMsg)

private[quint] case class QuintLookupTableEntry(
    kind: String,
    reference: Int)
private[quint] object QuintLookupTableEntry {
  implicit val rw: RW[QuintLookupTableEntry] = macroRW
}

/** The JSON output produced by quint parse */
private[quint] case class QuintOutput(
    stage: String,
    modules: Seq[QuintModule],
    // Maps source IDs to types, see the `WithId` trait
    types: Map[Int, QuintTypeScheme],
    // Maps name IDs to declaration IDs
    table: Map[Int, QuintLookupTableEntry])

private[quint] object QuintOutput {
  implicit val rw: RW[QuintOutput] = macroRW

  def read(s: ujson.Readable): Try[QuintOutput] =
    Try(QuintDeserializer.read[QuintOutput](s)).recoverWith { case err: upickle.core.AbortException =>
      scala.util.Failure(new QuintIRParseError(err.clue))
    }
}

private[quint] case class QuintModule(
    id: Int,
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
  val id: Int
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
  @key("name") case class QuintName(id: Int, name: String) extends QuintEx {}
  object QuintName {
    implicit val rw: RW[QuintName] = macroRW
  }

  /** The boolean literal value */
  @key("bool") case class QuintBool(id: Int, value: Boolean) extends QuintEx {}
  object QuintBool {
    implicit val rw: RW[QuintBool] = macroRW
  }

  @key("int") case class QuintInt(id: Int, value: Int) extends QuintEx {}
  object QuintInt {
    implicit val rw: RW[QuintInt] = macroRW
  }

  @key("str") case class QuintStr(id: Int, value: String) extends QuintEx {}
  object QuintStr {
    implicit val rw: RW[QuintStr] = macroRW
  }

  @key("app") case class QuintApp(
      id: Int,
      /** The name of the operator being applied */
      opcode: String,
      /** A list of arguments to the operator */
      args: Seq[QuintEx])
      extends QuintEx {}
  object QuintApp {
    implicit val rw: RW[QuintApp] = macroRW
  }

  case class QuintLambdaParameter(
      id: Int,
      name: String)
  object QuintLambdaParameter {
    implicit val rw: RW[QuintLambdaParameter] = macroRW
  }

  @key("lambda") case class QuintLambda(
      id: Int,
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
      id: Int,
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
  implicit val rw: RW[QuintDef] = RW.merge(QuintOpDef.rw, QuintVar.rw, QuintConst.rw, QuintAssume.rw, QuintTypeDef.rw)

  trait WithOptionalTypeAnnotation {
    val typeAnnotation: Option[QuintType]
  }

  trait WithTypeAnnotation {
    val typeAnnotation: QuintType
  }

  /**
   * A user-defined operator
   *
   * Note that QuintOpDef does not have any formal parameters. If an operator definition has formal parameters, then
   * `expr` is a lambda expression over those parameters.
   */
  @key("def") case class QuintOpDef(
      id: Int,
      /** definition name */
      name: String,
      /** qualifiers that identify definition kinds, like `def`, `val`, etc. */
      qualifier: String,
      /** expression to be associated with the definition */
      expr: QuintEx,
      typeAnnotation: Option[QuintType] = None)
      extends QuintDef with WithOptionalTypeAnnotation {}
  object QuintOpDef {
    implicit val rw: RW[QuintOpDef] = macroRW
  }

  @key("const") case class QuintConst(
      id: Int,
      /** name of the constant */
      name: String,
      typeAnnotation: QuintType)
      extends QuintDef with WithTypeAnnotation {}
  object QuintConst {
    implicit val rw: RW[QuintConst] = macroRW
  }

  @key("var") case class QuintVar(
      id: Int,
      /** name of the variable */
      name: String,
      typeAnnotation: QuintType)
      extends QuintDef with WithTypeAnnotation {}
  object QuintVar {
    implicit val rw: RW[QuintVar] = macroRW
  }

  @key("assume") case class QuintAssume(
      id: Int,
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
      id: Int,
      /** name of a type alias */
      name: String,
      /**
       * type to associate with the alias (none for uninterpreted type)
       *
       * Type aliases have `Some(type)` while abstract types have `None`
       */
      // TODO need special instruction for this conversion
      typ: Option[QuintType])
      extends QuintDef {}
  object QuintTypeDef {
    implicit val rw: RW[QuintTypeDef] = macroRW
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
