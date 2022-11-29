package at.forsyte.apalache.io.tnt

// This package uses upickle's macros to generate serialization functions for
// the TNT AST and associated output data.
//
// See https://com-lihaoyi.github.io/upickle/#Builtins for documentation on
// upickle semi-automatic JSON serialization docs.

// The `key` package allows customizing the JSON key for a class tag or attribute
// See https://com-lihaoyi.github.io/upickle/#CustomKeys
import upickle.implicits.key
import scala.util.Try

// We use a slightly customized deserializer
private[tnt] object TntDeserializer extends upickle.AttributeTagged {

  // By default, upickle uses the key `"$type"` to differentiate cases of a case
  // class, but TNT uses the key `"kind"` to encode the variant tag. This
  // override forms a custom deserializer that is just like the default, except
  // the value of "kind" is used to differentiate
  override def tagName = "kind"

}

import TntDeserializer.{macroRW, ReadWriter => RW}

private[tnt] class TntIRParseError(errMsg: String)
    extends Exception("Input was not a valid representation of the TntIR: " + errMsg)

/** The JSON output produced by tntc parse */
private[tnt] case class TntcOutput(
    status: String,
    module: TntModule,
    // Maps source IDs to types, see the `WithId` trait
    types: Map[Int, TntTypeScheme])

private[tnt] object TntcOutput {
  implicit val rw: RW[TntcOutput] = macroRW

  def read(s: ujson.Readable): Try[TntcOutput] =
    Try(TntDeserializer.read[TntcOutput](s)).recoverWith { case err: upickle.core.AbortException =>
      scala.util.Failure(new TntIRParseError(err.clue))
    }
}

private[tnt] case class TntModule(
    id: Int,
    name: String,
    defs: List[TntDef])
private[tnt] object TntModule {
  implicit val rw: RW[TntModule] = macroRW
}

/** The representation of types in the type map */
private[tnt] case class TntTypeScheme(
    @key("type") typ: TntType
    // TODO Will we need these for anything?
    // typeVariables: List[String],
    // rowVariables: List[String]
  )
private[tnt] object TntTypeScheme {
  implicit val rw: RW[TntTypeScheme] = macroRW
}

/** Source IDs, used to associate expressions with their inferred types */
private[tnt] trait WithID {
  val id: Int
}

/** The representation of TNT expressions */
sealed private[tnt] trait TntEx extends WithID

private[tnt] object TntEx {

  implicit val rw: RW[TntEx] =
    RW.merge(TntName.rw, TntBool.rw, TntInt.rw, TntStr.rw, TntApp.rw, TntLambda.rw, TntLet.rw)

  /** A name of: a variable, constant, parameter, user-defined operator */
  @key("name") case class TntName(id: Int, name: String) extends TntEx {}
  object TntName {
    implicit val rw: RW[TntName] = macroRW
  }

  /** The boolean literal value */
  @key("bool") case class TntBool(id: Int, value: Boolean) extends TntEx {}
  object TntBool {
    implicit val rw: RW[TntBool] = macroRW
  }

  @key("int") case class TntInt(id: Int, value: Int) extends TntEx {}
  object TntInt {
    implicit val rw: RW[TntInt] = macroRW
  }

  @key("str") case class TntStr(id: Int, value: String) extends TntEx {}
  object TntStr {
    implicit val rw: RW[TntStr] = macroRW
  }

  @key("app") case class TntApp(
      id: Int,
      /** The name of the operator being applied */
      opcode: String,
      /** A list of arguments to the operator */
      args: List[TntEx])
      extends TntEx {}
  object TntApp {
    implicit val rw: RW[TntApp] = macroRW
  }

  @key("lambda") case class TntLambda(
      id: Int,
      /** Identifiers for the formal parameters */
      params: List[String],
      /** The qualifier for the defined operator */
      // TODO should this eventually be a sumtype?
      qualifier: String,
      /** The definition body */
      expr: TntEx)
      extends TntEx {}
  object TntLambda {
    implicit val rw: RW[TntLambda] = macroRW
  }

  @key("let") case class TntLet(
      id: Int,
      /** The operator being defined for use in the body */
      opdef: TntDef.TntOpDef,
      /** The body */
      expr: TntEx)
      extends TntEx {}
  object TntLet {
    implicit val rw: RW[TntLet] = macroRW
  }
}

/** TNT Definitions (e.g., of types, operators, constants, etc.) */
sealed private[tnt] trait TntDef extends WithID

private[tnt] object TntDef {
  implicit val rw: RW[TntDef] = RW.merge(TntOpDef.rw, TntVar.rw, TntConst.rw, TntAssume.rw, TntTypeDef.rw)

  trait WithOptionalTypeAnnotation {
    val typeAnnotation: Option[TntType]
  }

  trait WithTypeAnnotation {
    val typeAnnotation: TntType
  }

  /**
   * A user-defined operator
   *
   * Note that * TntOpDef does not have any formal parameters. If an operator definition has formal parameters, then
   * `expr` is a lambda expression over those parameters.
   */
  @key("def") case class TntOpDef(
      id: Int,
      /** definition name */
      name: String,
      /** qualifiers that identify definition kinds, like `def`, `val`, etc. */
      qualifier: String,
      /** expression to be associated with the definition */
      expr: TntEx,
      typeAnnotation: Option[TntType] = None)
      extends TntDef with WithOptionalTypeAnnotation {}
  object TntOpDef {
    implicit val rw: RW[TntOpDef] = macroRW
  }

  @key("const") case class TntConst(
      id: Int,
      /** name of the constant */
      name: String,
      typeAnnotation: TntType)
      extends TntDef with WithTypeAnnotation {}
  object TntConst {
    implicit val rw: RW[TntConst] = macroRW
  }

  @key("var") case class TntVar(
      id: Int,
      /** name of the variable */
      name: String,
      typeAnnotation: TntType)
      extends TntDef with WithTypeAnnotation {}
  object TntVar {
    implicit val rw: RW[TntVar] = macroRW
  }

  @key("assume") case class TntAssume(
      id: Int,
      /** name of the assumption, may be '_' */
      name: String,
      /** an expression to associate with the name */
      assumption: TntEx)
      extends TntDef {}
  object TntAssume {
    implicit val rw: RW[TntAssume] = macroRW
  }

  /**
   * TntTypeDefs represent both type aliases and abstract types
   *
   *   - Abstract types do not have an associated `type`
   *   - Type aliases always have an associated `type`
   */
  @key("typedef") case class TntTypeDef(
      id: Int,
      /** name of a type alias */
      name: String,
      /**
       * type to associate with the alias (none for uninterpreted type)
       *
       * Type aliases have `Some(type)` while abstract types have `None`
       */
      // TODO need special instruction for this conversion
      typ: Option[TntType])
      extends TntDef {}
  object TntTypeDef {
    implicit val rw: RW[TntTypeDef] = macroRW
  }
}

/**
 * TNT Types
 *
 * Note that TNT types have an optional associated source ID. We ignore that in our representation currently, as we have
 * no use for source IDs on types.
 */
sealed private[tnt] trait TntType

private[tnt] object TntType {

  implicit val rw: RW[TntType] = RW.merge(
      TntBoolT.rw,
      TntIntT.rw,
      TntStrT.rw,
      TntConstT.rw,
      TntVarT.rw,
      TntSetT.rw,
      TntSeqT.rw,
      TntFunT.rw,
      TntOperT.rw,
      TntTupleT.rw,
      TntRecordT.rw,
      TntUnionT.rw,
  )

  // NOTE: Contrary to TNT values, for TNT types, source IDs are optional.
  // This is because many types are inferred, and not derived from the soruce.
  //
  // We therefor default id to -1 in the following, because upickle handles
  // optional values stupidly and if we specify `id` as `Option[Int]` it will
  // require the value of the ID field to be a (possibly empty) singleton array.

  @key("bool") case class TntBoolT() extends TntType {}
  object TntBoolT {
    implicit val rw: RW[TntBoolT] = macroRW
  }

  @key("int") case class TntIntT() extends TntType
  object TntIntT {
    implicit val rw: RW[TntIntT] = macroRW
  }

  @key("str") case class TntStrT() extends TntType
  object TntStrT {
    implicit val rw: RW[TntStrT] = macroRW
  }

  @key("const") case class TntConstT(name: String) extends TntType
  object TntConstT {
    implicit val rw: RW[TntConstT] = macroRW
  }

  @key("var") case class TntVarT(name: String) extends TntType
  object TntVarT {
    implicit val rw: RW[TntVarT] = macroRW
  }

  @key("set") case class TntSetT(elem: TntType) extends TntType
  object TntSetT {
    implicit val rw: RW[TntSetT] = macroRW
  }

  @key("list") case class TntSeqT(elem: TntType) extends TntType
  object TntSeqT {
    implicit val rw: RW[TntSeqT] = macroRW
  }

  @key("fun") case class TntFunT(arg: TntType, res: TntType) extends TntType
  object TntFunT {
    implicit val rw: RW[TntFunT] = macroRW
  }

  @key("oper") case class TntOperT(args: List[TntType], res: TntType) extends TntType
  object TntOperT {
    implicit val rw: RW[TntOperT] = macroRW
  }

  case class RecordField(fieldName: String, fieldType: TntType)
  object RecordField {
    implicit val rw: RW[RecordField] = macroRW
  }

  sealed trait Row

  object Row {
    implicit val rw: RW[Row] = RW.merge(Cell.rw, Var.rw, Nil.rw)

    @key("row") case class Cell(fields: List[RecordField], other: Row) extends Row
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

  @key("tup") case class TntTupleT(fields: Row) extends TntType
  object TntTupleT {
    implicit val rw: RW[TntTupleT] = macroRW
  }

  @key("rec") case class TntRecordT(fields: Row) extends TntType
  object TntRecordT {
    implicit val rw: RW[TntRecordT] = macroRW
  }

  case class UnionRecord(tagValue: String, fields: Row)
  object UnionRecord {
    implicit val rw: RW[UnionRecord] = macroRW
  }

  @key("union") case class TntUnionT(tag: String, records: List[UnionRecord]) extends TntType
  object TntUnionT {
    implicit val rw: RW[TntUnionT] = macroRW
  }
}
