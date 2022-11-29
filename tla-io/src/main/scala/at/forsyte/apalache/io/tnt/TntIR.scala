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
object TntDeserializer extends upickle.AttributeTagged {

  // By default, upickle uses the key `"$type"` to differentiate cases of a case
  // class, but TNT uses the key `"kind"` to encode the variant tag. This
  // override forms a custom deserializer that is just like the default, except
  // the value of "kind" is used to differentiate
  override def tagName = "kind"

}

import TntDeserializer.{macroRW, ReadWriter => RW}

class TntIRParseError(errMsg: String) extends Exception("Input was not a valid representation of the TntIR: " + errMsg)

/** The JSON output produced by tntc parse */
case class TntcOutput(
    status: String,
    module: TntModule,
    // Maps source IDs to types, see the `WithId` trait
    types: Map[Int, TntTypeScheme])

object TntcOutput {
  implicit val rw: RW[TntcOutput] = macroRW

  def read(s: ujson.Readable): Try[TntcOutput] =
    Try(TntDeserializer.read[TntcOutput](s)).recoverWith { case err: upickle.core.AbortException =>
      scala.util.Failure(new TntIRParseError(err.clue))
    }
}

case class TntModule(
    id: Int,
    name: String,
    defs: List[TntDef])
object TntModule {
  implicit val rw: RW[TntModule] = macroRW
}

/** The representation of types in the type map */
case class TntTypeScheme(
    @key("type") typ: TntType
    // TODO Will we need these for anything?
    // typeVariables: List[String],
    // rowVariables: List[String]
  )
object TntTypeScheme {
  implicit val rw: RW[TntTypeScheme] = macroRW
}

/** Source IDs, used to associate expressions with their inferred types */
trait WithID {
  val id: Int
}

/** The representation of TNT expressions */
sealed trait TntEx extends WithID

object TntEx {

  implicit val rw: RW[TntEx] =
    RW.merge(Name.rw, Bool.rw, TntInt.rw, Str.rw, App.rw, Lambda.rw, Let.rw)

  /** A name of: a variable, constant, parameter, user-defined operator */
  @key("name") case class Name(id: Int, name: String) extends TntEx {}
  object Name {
    implicit val rw: RW[Name] = macroRW
  }

  /** The boolean literal value */
  @key("bool") case class Bool(id: Int, value: Boolean) extends TntEx {}
  object Bool {
    implicit val rw: RW[Bool] = macroRW
  }

  @key("int") case class TntInt(id: Int, value: Int) extends TntEx {}
  object TntInt {
    implicit val rw: RW[TntInt] = macroRW
  }

  @key("str") case class Str(id: Int, value: String) extends TntEx {}
  object Str {
    implicit val rw: RW[Str] = macroRW
  }

  @key("app") case class App(
      id: Int,
      /** The name of the operator being applied */
      opcode: String,
      /** A list of arguments to the operator */
      args: List[TntEx])
      extends TntEx {}
  object App {
    implicit val rw: RW[App] = macroRW
  }

  @key("lambda") case class Lambda(
      id: Int,
      /** Identifiers for the formal parameters */
      params: List[String],
      /** The qualifier for the defined operator */
      // TODO should this eventually be a sumtype?
      qualifier: String,
      /** The definition body */
      expr: TntEx)
      extends TntEx {}
  object Lambda {
    implicit val rw: RW[Lambda] = macroRW
  }

  @key("let") case class Let(
      id: Int,
      /** The operator being defined for use in the body */
      opdef: TntDef.Def,
      /** The body */
      expr: TntEx)
      extends TntEx {}
  object Let {
    implicit val rw: RW[Let] = macroRW
  }
}

/** TNT Definitions (e.g., of types, operators, constants, etc.) */
sealed trait TntDef extends WithID

object TntDef {
  implicit val rw: RW[TntDef] = RW.merge(Def.rw, Var.rw, Const.rw, Assume.rw, TypeDef.rw)

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
  @key("def") case class Def(
      id: Int,
      /** definition name */
      name: String,
      /** qualifiers that identify definition kinds, like `def`, `val`, etc. */
      qualifier: String,
      /** expression to be associated with the definition */
      expr: TntEx,
      typeAnnotation: Option[TntType] = None)
      extends TntDef with WithOptionalTypeAnnotation {}
  object Def {
    implicit val rw: RW[Def] = macroRW
  }

  @key("const") case class Const(
      id: Int,
      /** name of the constant */
      name: String,
      typeAnnotation: TntType)
      extends TntDef with WithTypeAnnotation {}
  object Const {
    implicit val rw: RW[Const] = macroRW
  }

  @key("var") case class Var(
      id: Int,
      /** name of the variable */
      name: String,
      typeAnnotation: TntType)
      extends TntDef with WithTypeAnnotation {}
  object Var {
    implicit val rw: RW[Var] = macroRW
  }

  @key("assume") case class Assume(
      id: Int,
      /** name of the assumption, may be '_' */
      name: String,
      /** an expression to associate with the name */
      assumption: TntEx)
      extends TntDef {}
  object Assume {
    implicit val rw: RW[Assume] = macroRW
  }

  /**
   * TntTypeDefs represent both type aliases and abstract types
   *
   *   - Abstract types do not have an associated `type`
   *   - Type aliases always have an associated `type`
   */
  @key("typedef") case class TypeDef(
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
  object TypeDef {
    implicit val rw: RW[TypeDef] = macroRW
  }
}

/**
 * TNT Types
 *
 * Note that TNT types have an optional associated source ID. We ignore that in our representation currently, as we have
 * no use for source IDs on types.
 */
sealed trait TntType

object TntType {

  implicit val rw: RW[TntType] = RW.merge(
      BoolT.rw,
      IntT.rw,
      StrT.rw,
      ConstT.rw,
      VarT.rw,
      SetT.rw,
      SeqT.rw,
      FunT.rw,
      OperT.rw,
      TupleT.rw,
      RecordT.rw,
      UnionT.rw,
  )

  // NOTE: Contrary to TNT values, for TNT types, source IDs are optional.
  // This is because many types are inferred, and not derived from the soruce.
  //
  // We therefor default id to -1 in the following, because upickle handles
  // optional values stupidly and if we specify `id` as `Option[Int]` it will
  // require the value of the ID field to be a (possibly empty) singleton array.

  @key("bool") case class BoolT() extends TntType {}
  object BoolT {
    implicit val rw: RW[BoolT] = macroRW
  }

  @key("int") case class IntT() extends TntType
  object IntT {
    implicit val rw: RW[IntT] = macroRW
  }

  @key("str") case class StrT() extends TntType
  object StrT {
    implicit val rw: RW[StrT] = macroRW
  }

  @key("const") case class ConstT(name: String) extends TntType
  object ConstT {
    implicit val rw: RW[ConstT] = macroRW
  }

  @key("var") case class VarT(name: String) extends TntType
  object VarT {
    implicit val rw: RW[VarT] = macroRW
  }

  @key("set") case class SetT(elem: TntType) extends TntType
  object SetT {
    implicit val rw: RW[SetT] = macroRW
  }

  @key("list") case class SeqT(elem: TntType) extends TntType
  object SeqT {
    implicit val rw: RW[SeqT] = macroRW
  }

  @key("fun") case class FunT(arg: TntType, res: TntType) extends TntType
  object FunT {
    implicit val rw: RW[FunT] = macroRW
  }

  @key("oper") case class OperT(args: List[TntType], res: TntType) extends TntType
  object OperT {
    implicit val rw: RW[OperT] = macroRW
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

  @key("tup") case class TupleT(fields: Row) extends TntType
  object TupleT {
    implicit val rw: RW[TupleT] = macroRW
  }

  @key("rec") case class RecordT(fields: Row) extends TntType
  object RecordT {
    implicit val rw: RW[RecordT] = macroRW
  }

  case class UnionRecord(tagValue: String, fields: Row)
  object UnionRecord {
    implicit val rw: RW[UnionRecord] = macroRW
  }

  @key("union") case class UnionT(tag: String, records: List[UnionRecord]) extends TntType
  object UnionT {
    implicit val rw: RW[UnionT] = macroRW
  }
}
